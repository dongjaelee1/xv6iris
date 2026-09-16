/-
Specification of `sleep` (kernel/proc.c), this kernel's half of the
sleep/wakeup protocol that actually parks:

  void sleep(void) {
    struct proc *p = myproc();
    acquire(&p->lock);
    if(p->chan != 0) { p->state = SLEEPING; sched(); }
    release(&p->lock);
  }

The channel was published by `sleep_prepare` under the same lock; `sleep`
re-takes the lock and parks only if it is still set (a `wakeup` that ran in
between cleared it, and then `sleep` is a no-op).

The shape is `yield`'s: entered with interrupts off at depth 0 holding no
lock, with a process running on this hart (`cpuClaim cpu k.proc`, the
claim's two ghost halves), it may cross into the scheduler, so the thread
returns on WHICHEVER hart resumed it -- the trap CSRs, the claim and the
installed handler it gets back are that hart's, and its `SPIE`/`SPP` are
that hart's too.

THE KERNEL ROOT IS QUANTIFIED AS WELL (`sleepExitK`): `sched`'s resumed
configuration is `resumedK .. root' ..` with the RESUMING hart's kernel
page-table root, and nothing in the crossing ties it to the parking hart's.
(`Xv6.SpecYield`'s assumed contract, which returns the caller's own
`k.root`, is stronger than what the crossing gives.)

Imports only definitional files.
-/
import Xv6.SchedCtx
import MachCSL.WpSmodeIntr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `sleep`. -/
def sleepAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«sleep»

/-- The stack `sleep`'s cone needs: its own 4-slot frame over `sched`'s 16. -/
def sleepSlots : Nat := 20

/-- The configuration `sleep` returns in: the caller's, with the registers,
the `SPIE`/`SPP` the last `push_off` pinned and the kernel page-table root
of the hart the scheduler resumed the thread on. -/
def sleepExitK (k : KCtx) (spie spp : Bool) (root : BitVec 44) (R : RegMap) : KCtx :=
  { k with regs := R, spie := spie, spp := spp, root := root }

@[simp] theorem sleepExitK_regs (k : KCtx) (a b : Bool) (r : BitVec 44) (R : RegMap) :
    (sleepExitK k a b r R).regs = R := rfl
@[simp] theorem sleepExitK_sie (k : KCtx) (a b : Bool) (r : BitVec 44) (R : RegMap) :
    (sleepExitK k a b r R).sie = k.sie := rfl
@[simp] theorem sleepExitK_spie (k : KCtx) (a b : Bool) (r : BitVec 44) (R : RegMap) :
    (sleepExitK k a b r R).spie = a := rfl
@[simp] theorem sleepExitK_spp (k : KCtx) (a b : Bool) (r : BitVec 44) (R : RegMap) :
    (sleepExitK k a b r R).spp = b := rfl
@[simp] theorem sleepExitK_avail (k : KCtx) (a b : Bool) (r : BitVec 44) (R : RegMap) :
    (sleepExitK k a b r R).avail = k.avail := rfl
@[simp] theorem sleepExitK_noff (k : KCtx) (a b : Bool) (r : BitVec 44) (R : RegMap) :
    (sleepExitK k a b r R).noff = k.noff := rfl
@[simp] theorem sleepExitK_intena (k : KCtx) (a b : Bool) (r : BitVec 44) (R : RegMap) :
    (sleepExitK k a b r R).intena = k.intena := rfl
@[simp] theorem sleepExitK_locks (k : KCtx) (a b : Bool) (r : BitVec 44) (R : RegMap) :
    (sleepExitK k a b r R).locks = k.locks := rfl
@[simp] theorem sleepExitK_tier (k : KCtx) (a b : Bool) (r : BitVec 44) (R : RegMap) :
    (sleepExitK k a b r R).tier = k.tier := rfl
@[simp] theorem sleepExitK_root (k : KCtx) (a b : Bool) (r : BitVec 44) (R : RegMap) :
    (sleepExitK k a b r R).root = r := rfl
@[simp] theorem sleepExitK_proc (k : KCtx) (a b : Bool) (r : BitVec 44) (R : RegMap) :
    (sleepExitK k a b r R).proc = k.proc := rfl
@[simp] theorem sleepExitK_sp (k : KCtx) (a b : Bool) (r : BitVec 44) (R : RegMap) :
    (sleepExitK k a b r R).sp = R 2#5 := rfl

@[simp] theorem sleepExitK_withRegs (k : KCtx) (a b : Bool) (r : BitVec 44) (R R' : RegMap) :
    (sleepExitK k a b r R).withRegs R' = sleepExitK k a b r R' := rfl

/-- The no-park exit: nothing moved. -/
theorem sleepExitK_self (k : KCtx) (R : RegMap) :
    sleepExitK k k.spie k.spp k.root R = k.withRegs R := by
  cases k; rfl

/-- **WP of `sleep`.** -/
def wp_sleep_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (j : Nat)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : sleepSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu sleepAddr ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ root' : BitVec 44,
    ∀ R' : RegMap,
    kctx cpu' (sleepExitK k spie spp root' R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `sleep`. -/
structure SLEEP : Prop where
  wp_sleep : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (j : Nat) hj hproc hK hsie hnoff hlocks htier,
    wp_sleep_body (hlc := hlc) (GF := GF) Γ cpu k j hj hproc hK hsie hnoff hlocks htier

end Xv6
