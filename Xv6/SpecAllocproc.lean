/-
Specification of `allocproc` (kernel/proc.c): the scan for an UNUSED slot
(each lock taken and released in turn), then, holding its lock: a fresh
pid (the inlined `allocpid`, under `pid_lock`), USED, a trapframe page
from `kalloc`, a user table from `proc_pagetable`, the context zeroed
with `ra = forkret` and `sp = kstack + PGSIZE`; the failure tails run
`freeproc` and return `0` with the lock released.  Uncounted (`on`);
needs 48 slots.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import MachCSL.Lock
import Xv6.SchedCtx
import Xv6.PidLock
import Xv6.SpecProcPagetable
import Xv6.Image
import Xv6.Geom

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

def allocprocAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«allocproc»
def forkretAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«forkret»
def allocprocSlots : Nat := 48

/-- The private block `allocproc` builds: no files, no cwd, size 0, an
empty space, the context `[forkret, kstack + PGSIZE, 0 × 12]`. -/
def allocprocPriv (V : ProcPriv) : Prop :=
  V.ofile = List.replicate NOFILE 0#64 ∧ V.cwd = 0#64 ∧ V.sz = 0#64 ∧
  (∀ vpn, Iris.Std.PartialMap.get? V.upt.um vpn = none) ∧
  V.context = [forkretAddr, V.kstack + 4096#64] ++ List.replicate 12 0#64

/-- `allocproc`'s result. -/
def allocprocPost {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) (cpu : CPU) (γk : KmemNames) (on : Option Nat) (r : BitVec 64) : IProp GF := iprop%
  (⌜r = 0#64⌝ ∗ ∃ on' : Option Nat, ⌜on' = on ∨ on' = none⌝ ∗ kallocAvail γk on') ∨
  (∃ (j : Nat) (ch : BitVec 64) (pid : BitVec 32) (V : ProcPriv) (M : Nat → List (BitVec 8)) (g : Nat),
    ⌜r = procAddr j ∧ j < NPROC ∧ 1 ≤ pid.toNat ∧ pid.toNat ≤ PIDMAX ∧ allocprocPriv V ∧ g ≤ procPagetableNodes + 1⌝ ∗
    procHeld Γ cpu j USED ch ∗ hartAtAny Γ (procAddr j) ∗
    procPriv (procAddr j) pid V M ∗ stackOwn (V.kstack + 4096#64) 512 ∗ kallocAvail γk (availSub on g))

def wp_allocproc_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (Γ : SchedNames) (cpu : CPU) (k : KCtx) (γl γp : GName) (γk : KmemNames) (on : Option Nat)
    (hnoff : k.noff + 2 < 2 ^ 31) (hK : allocprocSlots ≤ k.avail)
    (hlk : "kmem" ∉ k.locks) (hlp : "nextpid" ∉ k.locks) (hlq : "proc" ∉ k.locks) (htier : k.tier = KTier.kpt) : Prop :=
  kctx cpu k ∗ pcIs cpu allocprocAddr ∗ procsInv Γ ∗
  isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗ isLock γp pidLockAddr "nextpid" pidLockPay ∗ kallocAvail γk on ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ R' : RegMap,
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    ((⌜R' 10#5 = 0#64⌝ ∗ kctx cpu' ((k.withSpie spie spp).withRegs R')) ∨
     (⌜R' 10#5 ≠ 0#64⌝ ∗ kctx cpu' (((k.pushOffAt spie spp).withRegs R').withLocks ("proc" :: k.locks)))) -∗
    pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    allocprocPost Γ cpu' γk on (R' 10#5) -∗
    ⌜calleeSaved k.regs R'⌝ -∗ wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

structure ALLOCPROC : Prop where
  wp_allocproc : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (Γ : SchedNames) (cpu : CPU) (k : KCtx)
    (γl γp : GName) (γk : KmemNames) (on : Option Nat) hnoff hK hlk hlp hlq htier,
    wp_allocproc_body (hlc := hlc) (GF := GF) Γ cpu k γl γp γk on hnoff hK hlk hlp hlq htier

end Xv6
