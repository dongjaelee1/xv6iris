/-
Specification of `mappages` (kernel/vm.c): the public contract, stated
once, in the kernel execution context.

`mappages(pagetable, va, size, pa, perm)` maps the `n = size / PGSIZE`
pages from `va` to the pages from `pa` with `perm`, walking (with
allocation) to each level-0 entry and writing the leaf; it panics on a
misaligned `va`/`pa`, a zero size, or an entry already valid.  Stated in
the counted mode only (the Rocq `wp_mappages_sconf`'s live arm): the
caller's count of free pages exceeds the nodes the run creates
(`missingRun`), so no `walk` fails and the result is `0`, the tree
`PTree.mapRun` over the pages `kalloc` handed out.  The tree's pages are
required to be valid allocator pages (`hpg`), as `walk` needs.  Stated at
either interrupt index (the exit as `kalloc`'s).  The function needs 32 of the
caller's stack slots (its frame of 10, then `walk`'s 22) and returns
them; the callee-saved registers are preserved.

Imports only definitional files (never a `Code*` or `Proof*` file).
-/
import MachCSL.WpSmodeFrame
import MachCSL.Lock
import Xv6.PtOwn
import Xv6.Image
import Xv6.Geom

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Std MachCSL
open LeanRV64D

/-- Address of `mappages`. -/
def mappagesAddr : BitVec 64 := BitVec.ofNat 64 KernelSyms.«mappages»

/-- The pure premises of a run: aligned `va`/`pa`, `n ≥ 1` pages, in range,
every page of the run unmapped. -/
def mappagesArgs (t : PTree) (va size pa : BitVec 64) (n : Nat) : Prop :=
  va &&& 0xfff#64 = 0#64 ∧ pa &&& 0xfff#64 = 0#64 ∧
  size = BitVec.ofNat 64 (4096 * n) ∧ 1 ≤ n ∧
  va.toNat + 4096 * n ≤ 2 ^ 38 ∧ pa.toNat + 4096 * n < 2 ^ 56 ∧
  ∀ i, i < n → t.walk 2 (vpnOf va + BitVec.ofNat 27 i) = none

/-- The specification of `mappages` (counted mode). -/
def wp_mappages_body {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx]
    (cpu : CPU) (k : KCtx) (γl : GName) (γk : KmemNames) (nb : Nat) (t : PTree) (n : Nat) (perm : KPerm)
    (hnoff : k.noff + 1 < 2 ^ 31) (hK : 32 ≤ k.avail) (hlk : "kmem" ∉ k.locks)
    (hroot : k.regs 10#5 = pageAddr t.base)
    (hargs : mappagesArgs t (k.regs 11#5) (k.regs 12#5) (k.regs 13#5) n)
    (hperm : k.regs 14#5 = permBits perm)
    (hwf : t.wf 2) (hnd : t.pagesNodup 2)
    (hpg : ∀ b ∈ t.pages 2, pageValid (pageAddr b))
    (hcount : t.missingRun (vpnOf (k.regs 11#5)) n < nb) : Prop :=
  kctx cpu k ∗ pcIs cpu mappagesAddr ∗ isLock γl kmemLockAddr "kmem" (kmemRes γk) ∗
  ptreeOwn 2 (DFrac.own 1) t ∗ kallocAvail γk (some nb) ∗
  wpNext k.sie k.proc cpu (fun cpu' => iprop(∀ spie : Bool, ∀ spp : Bool, ∀ (R' : RegMap) (fresh : List (BitVec 44)),
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ptreeOwn 2 (DFrac.own 1)
      (t.mapRun (vpnOf (k.regs 11#5)) (BitVec.extractLsb' 12 44 (k.regs 13#5)) perm n fresh).1 -∗
    kallocAvail γk (some (nb - fresh.length)) -∗
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = 0#64 ∧
      fresh.length = t.missingRun (vpnOf (k.regs 11#5)) n ∧
      (t.mapRun (vpnOf (k.regs 11#5)) (BitVec.extractLsb' 12 44 (k.regs 13#5)) perm n fresh).2 = ([], n) ∧
      fresh.Nodup ∧ (∀ b ∈ fresh, pageValid (pageAddr b) ∧ b ∉ t.pages 2)⌝ -∗
    wpLoop cpu'))
  ⊢ wpLoop (GF := GF) cpu

/-- The interface of `mappages`. -/
structure MAPPAGES : Prop where
  wp_mappages : ∀ {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [CurCtx] (cpu : CPU) (k : KCtx)
    (γl : GName) (γk : KmemNames) (nb : Nat) (t : PTree) (n : Nat) (perm : KPerm)
    hnoff hK hlk hroot hargs hperm hwf hnd hpg hcount,
    wp_mappages_body (hlc := hlc) (GF := GF) cpu k γl γk nb t n perm hnoff hK hlk hroot hargs hperm hwf hnd hpg hcount

end Xv6
