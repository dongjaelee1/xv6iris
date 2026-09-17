/-
Specification of `userinit` (kernel/proc.c), the first process:

    void userinit(void) {
      struct proc *p = allocproc();
      initproc = p;
      p->cwd = namei("/");
      p->state = RUNNABLE;
      release(&p->lock);
    }

BOOT CODE: it runs on the boot hart before any scheduler does, so there
is no process on this hart (`k.proc = 0`), no claim and no parking.  Both
of its callees are fine with that -- `allocproc` never calls `myproc` and
is generic in the interrupt index, and `namei` is taken at the boot arm of
the file-system boundary (`Xv6.FsEnv.wp_boot_blocking_body`: at boot there
is nothing to sleep on).

IT PUBLISHES `initproc`.  The word at `&initproc` is written exactly once,
here, and read forever after (`kexit`'s "init exiting" check, `reparent`'s
target), so `userinit` takes it owned and gives it back DISCARDED, as the
persistent `initprocIs` every later reader takes as a premise.

COUNTED: `allocproc` needs a trapframe page and up to
`procPagetableNodes` table nodes, so the caller lends `kallocAvail γk
(some nb)` with `nb` over that bound and gets back what is left.  The
whole of the first process -- its block, its kernel stack, its parked
`forkret` record (`Xv6/ForkretRecord.lean`, whence `[ForkretIs]`) -- goes
into `procsInv` at the closing `release`, and the slot is left RUNNABLE
for the first scheduler that looks.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import Xv6.SchedCtx
import Xv6.WaitLock
import Xv6.PidLock
import Xv6.FsEnv
import Xv6.SpecForkret
import Xv6.SpecAllocproc
import MachCSL.Lock
import MachCSL.WpSmodeIntr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `userinit`. -/
def userinitAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«userinit»

/-- The stack `userinit`'s cone needs: its own 4-slot frame over `namei`'s
(`allocproc` needs 48). -/
def userinitSlots : Nat := 4 + fsSlots

/-- **WP of `userinit`.** -/
def wp_userinit_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γp γl : GName) (γk : KmemNames) (nb : Nat)
    (hnoff : k.noff + 2 < 2 ^ 31) (hnoff0 : k.noff = 0) (hK : userinitSlots ≤ k.avail)
    (hlk : "kmem" ∉ k.locks) (hlp : "nextpid" ∉ k.locks) (hlq : "proc" ∉ k.locks)
    (hlocks : k.locks = []) (htier : k.tier = KTier.kpt) (hproc : k.proc = 0#64)
    (hnb : procPagetableNodes + 1 < nb) : Prop :=
  kctx cpu k ∗ pcIs cpu userinitAddr ∗ procsInv Γ ∗
  isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ isLock γp pidLockAddr "nextpid" pidLockPay ∗
  kallocAvail γk (some nb) ∗
  (∃ w : BitVec 64, wordPointsTo initprocAddr 8 (DFrac.own 1) w) ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ (spie spp : Bool) (R' : RegMap) (ip : BitVec 64)
    (g : Nat),
    ⌜(k.sie = false → spie = k.spie ∧ spp = k.spp) ∧ calleeSaved k.regs R' ∧
      g ≤ procPagetableNodes + 1 ∧ ∃ i : Nat, i < NPROC ∧ ip = procAddr i⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    initprocIs ip -∗ kallocAvail γk (availSub (some nb) g) -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `userinit`. -/
structure USERINIT : Prop where
  wp_userinit : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] [FsEnv] [ForkretIs]
    (cpu : CPU) (k : KCtx) (γp γl : GName) (γk : KmemNames) (nb : Nat)
    hnoff hnoff0 hK hlk hlp hlq hlocks htier hproc hnb,
    wp_userinit_body (hlc := hlc) (GF := GF) Γ cpu k γp γl γk nb
      hnoff hnoff0 hK hlk hlp hlq hlocks htier hproc hnb

end Xv6
