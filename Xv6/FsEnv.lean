/-
Xv6: the ASSUMED file-system interface.

The file system and user mode are not modelled.  The process code calls a
handful of fs entry points (`fileclose`, `begin_op`/`end_op`, `iput`,
`namei`, `filedup`, `idup`); every one of them may sleep, so its assumed
contract is SLEEP-SHAPED: exactly the premises and post of `wp_sleep_body`
(`Xv6.SpecSleep`) with the entry address abstracted -- the caller runs
with interrupts off at depth 0, holding no lock, on its own process; the
scheduler invariant, the trap CSRs, the hart's claim and the interrupt
resource go in and come back; callee-saved registers are preserved; the
return register is unconstrained (`fileclose(f)` ignores `f`;
`filedup`/`idup`/`namei` return some word).

The whole of `forkret` is assumed too (`Xv6.SpecForkret`): it runs `fsinit`
and `kexec` on the first process and returns to user mode through the
trampoline.

These are class assumptions in the style of `ClaimIs`/`EnvIs`: a proof
that needs them takes `[FsEnv GF]`.
-/
import Xv6.SpecSleep

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

def filecloseAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«fileclose»
def beginOpAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«begin_op»
def endOpAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«end_op»
def iputAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«iput»
def nameiAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«namei»
def filedupAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«filedup»
def idupAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«idup»

/-- The stack an fs entry point may use (assumed). -/
def fsSlots : Nat := 64

/-- **A blocking call** (the shape of `wp_sleep_body` at entry `entry`). -/
def wp_blocking_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (j : Nat) (entry : BitVec 64)
    (hj : j < NPROC) (hproc : k.proc = procAddr j) (hK : fsSlots ≤ k.avail)
    (hsie : k.sie = false) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu entry ∗ procsInv Γ ∗
  trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu ∗
  wpNext true k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    trapCsrs cpu' -∗ cpuClaim cpu' k.proc -∗ intrRes cpu' -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- **A blocking call made at BOOT**, before any process runs: `userinit`'s
`namei("/")`.  There is no process on this hart (`k.proc = 0`) and hence no
claim, no trap CSRs and no parking: a call that cannot sleep -- there is
nothing to sleep on -- so the shape is `wakeup`'s, not `sleep`'s (balanced,
generic in the interrupt index, the proc table in as the only environment).
The return register is unconstrained (`namei` returns some inode pointer).
-/
def wp_boot_blocking_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) (cpu : CPU) (k : KCtx) (entry : BitVec 64)
    (hK : fsSlots ≤ k.avail) (hnoff : k.noff = 0) (hlocks : k.locks = [])
    (htier : k.tier = KTier.kpt) (hproc : k.proc = 0#64) : Prop :=
  kctx cpu k ∗ pcIs cpu entry ∗ procsInv Γ ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The assumed contract of one fs entry point at boot. -/
def FsBootEntry (entry : BitVec 64) : Prop :=
  ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) (cpu : CPU) (k : KCtx) hK hnoff hlocks htier hproc,
    wp_boot_blocking_body (hlc := hlc) (GF := GF) Γ cpu k entry hK hnoff hlocks htier hproc

/-- The assumed contract of one fs entry point. -/
def FsEntry (entry : BitVec 64) : Prop :=
  ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) [ClaimIs (hlc := hlc) GF Γ]
    (cpu : CPU) (k : KCtx) (j : Nat) hj hproc hK hsie hnoff hlocks htier,
    wp_blocking_body (hlc := hlc) (GF := GF) Γ cpu k j entry hj hproc hK hsie hnoff hlocks htier

/-- **The file-system boundary** (assumed). -/
class FsEnv : Prop where
  fileclose : FsEntry filecloseAddr
  begin_op : FsEntry beginOpAddr
  end_op : FsEntry endOpAddr
  iput : FsEntry iputAddr
  namei : FsEntry nameiAddr
  filedup : FsEntry filedupAddr
  idup : FsEntry idupAddr
  /-- `userinit` calls `namei("/")` on the boot hart, where no process runs
  yet (`Xv6/SpecUserinit.lean`). -/
  nameiBoot : FsBootEntry nameiAddr

end Xv6
