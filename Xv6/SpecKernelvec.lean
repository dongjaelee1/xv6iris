/-
Specification of `kernelvec` (kernel/kernelvec.S), xv6's supervisor trap
vector.  Nothing calls it: the hardware traps to it.  Its contract is
therefore not a function spec but the trap engine's handler contract
`ihs ⟨cpu, kernelvec⟩` (`MachCSL.KCtx`): from the context a supervisor
interrupt leaves, the handler runs and resumes the interrupted context at
the trapped pc, on whichever hart the thread lands on.
Imports only definitional files.
-/
import Xv6.SchedCtx
import MachCSL.WpSmodeIntr

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `kernelvec`. -/
def kernelvecAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«kernelvec»

/-- `stvec := kernelvec` is a direct-mode vector. -/
theorem kernelvecAddr_direct : stvecDirect kernelvecAddr := by
  unfold stvecDirect kernelvecAddr KernelSyms.«kernelvec»; decide

/-- **The handler's environment**: the proc table's invariant AT EVERY
CONTEXT.  A trap arrives at whatever context the interrupted hart then
runs (`ihsF` quantifies it), and `procsInv` is context-relative (every
lock handle carries its creator's floor), so the handler contract -- a
`□` over all contexts -- can only close over an invariant it has at all
of them.  The Rocq prototype threads this as an environment FAMILY with a
transport law that the trap engine applies per trap
(`SpecKernelvec.kernelvec_env` / `IntrDefs.env_move`); `MachCSL.ihsF`
has no environment parameter yet, so the family is demanded up front.
Persistent. -/
def procsInvAll {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
    (Γ : SchedNames) : IProp GF :=
  iprop(∀ X : CurCtx, @procsInv hlc GF _ _ X Γ)

instance procsInvAll_persistent {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
    (Γ : SchedNames) : Persistent (procsInvAll (hlc := hlc) (GF := GF) Γ) := by
  unfold procsInvAll; infer_instance

/-- The interface of `kernelvec`: the handler contract, at every hart.

It is stated UNDER the handler's environment (persistent): kernelvec
calls `kerneltrap`, whose timer path yields, and `yield` needs the proc
table.  Nothing else about the interrupted context is assumed -- `ihsF`
quantifies it freely, and the running slot is named by THE CLAIM the trap
hands over (`Xv6.cpuClaim_proc_shape`). -/
structure KERNELVEC : Prop where
  handler : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ] (cpu : CPU),
    procsInvAll (GF := GF) Γ ⊢ ihs ⟨cpu, kernelvecAddr⟩

end Xv6
