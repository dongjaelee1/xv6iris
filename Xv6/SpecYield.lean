/-
Specification of `yield` (kernel/proc.c), ASSUMED as an interface for
now: the running process gives up the hart (the proc machinery --
p->lock, sched, swtch, the scheduler -- is not modeled yet).

Called with interrupts off at depth 0 with no lock held, with a process
running (`k.proc ≠ 0`) at the Kpt tier.  The thread returns to `ra` on
WHICHEVER hart the scheduler resumes it on: the per-hart resources it
carried in -- the trap CSRs, the proc claim, the installed handler -- are
the resumed hart's on exit, the callee-saved registers are preserved,
and the pinned `SPIE`/`SPP` are whatever that hart's are.
Imports only definitional files.
-/
import Xv6.Image
import Xv6.UartTrace
import MachCSL.WpSmodeIntr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `yield`. -/
def yieldAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«yield»

/-- The stack yield's cone needs. -/
def yieldSlots : Nat := 20

/-- **WP of `yield`.** -/
def wp_yield_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = []) (htier : k.tier = KTier.kpt)
    (hproc : k.proc ≠ 0#64) (hK : yieldSlots ≤ k.avail) : Prop :=
  kctx cpu k ∗ pcIs cpu yieldAddr ∗ trapCsrs cpu ∗ cpuClaim k.proc ∗ intrRes cpu ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim k.proc -∗ intrRes cpu' -∗ ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `yield`. -/
structure YIELD : Prop where
  wp_yield : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) hsie hnoff hlocks htier hproc hK,
    wp_yield_body (hlc := hlc) (GF := GF) cpu k hsie hnoff hlocks htier hproc hK

end Xv6
