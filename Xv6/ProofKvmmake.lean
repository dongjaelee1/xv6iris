/-
Proof of `kvmmake`'s specification (`SpecKvmmake.KVMMAKE`), given the
interfaces of `kalloc`, `memset`, `kvmmap` and `proc_mapstacks`.

The shape: the four-slot frame, `kalloc` for the root page (the failing
arm is dead in the counted mode), `memset` zeroing it into a zero node,
the six `kvmmap` calls of `kvmRegions` (`Xv6/ProofKvmRegions.lean`),
`proc_mapstacks` for the 64 kernel stacks (whose paths the trampoline's
mapping already completed, so they cost no nodes), and the epilogue.
Stated at either interrupt index, as its callees are.
-/
import Xv6.ProofKvmRegions

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D
open Xv6.Kvm

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

attribute [local semireducible] LeanRV64D.Functions.hartSupports LeanRV64D.Functions.currentlyEnabled

-- The tree constructions are never unfolded: with a literal page count
-- `whnf` duplicates the tree at every step.
attribute [local irreducible] MachCSL.PTree.mapRun MachCSL.PTree.mapStacks
attribute [local irreducible] MachCSL.PTree.fill MachCSL.PTree.missingRun MachCSL.PTree.missingStacks

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF]

/-! ## The caller's continuation, named -/

/-- `kvmmake`'s postcondition at the returning hart (the body of the
`wpNext` of `wp_kvmmake_body`), named so that it can be carried through the
region lemma as an opaque resource. -/
def kvmmakeCont [CurCtx] (k : KCtx) (γk : KmemNames) (nb : Nat) (cpu' : CPU) : IProp GF :=
  iprop(∀ spie : Bool, ∀ spp : Bool, ∀ (R' : RegMap) (t : PTree) (pas : Nat → BitVec 44),
    ⌜k.sie = false → spie = k.spie ∧ spp = k.spp⌝ -∗
    kctx cpu' ((k.withSpie spie spp).withRegs R') -∗ pcIs cpu' (jumpPc (k.regs 1#5)) -∗
    ptreeOwn 2 (DFrac.own 1) t -∗ kstackPages pas -∗
    kallocAvail γk (some (nb - kvmmakeCount)) -∗
    ⌜calleeSaved k.regs R' ∧ R' 10#5 = pageAddr t.base ∧ kvmTableOk t pas⌝ -∗
    wpLoop cpu')

/-! ## The function -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem kvmmake_proof (KA : KALLOC) (MS : MEMSET) (KM : KVMMAP) (PM : PROC_MAPSTACKS) : KVMMAKE :=
  ⟨fun {hlc GF} _ _ _ cpu k γl γk nb hnoff hK hlk hcount => by
  unfold wp_kvmmake_body
  simp only [kvmmakeAddr, KernelSyms.«kvmmake»]
  iintro ⟨Hk, Hpc, #Hlk, Hav, HΦ⟩
  icases kctx_kernelText _ _ $$ Hk with ⟨#Htext, Hk⟩
  k_norm_g
  -- the prologue
  iapply (wp_prologue4s1_gen cpu k 0x800010c2#64 (by omega))
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm_g
  iframe
  inext
  iapply wpNext_intro_pin
  iintro %c1 %hp1 Hk Hpc Hframe
  -- jal ra, kalloc
  k_step_gen (wp_s_jal c1 _ 0x800010cc#64 false 2095636#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] next c2 hp2
  iintro Hk Hpc
  iapply (km_kalloc_call KA c2 _ γl γk (some nb) ?hn1 ?hK1 ?hl1) $$ [- $Hk $Hpc]
  rotate_right 1
  k_norm_g
  iframe #
  iframe Hav
  case hn1 => k_norm_g; omega
  case hK1 => k_norm_g; omega
  case hl1 => k_norm_g; exact hlk
  k_norm_g
  iapply wpNext_intro_pin
  iintro %c3 %hp3 %spie1 %spp1 %R1 %hsp1 Hk Hpc HPost %hcs1
  k_norm_g [km_ret_10d0]
  unfold calleeSaved at hcs1
  k_norm_g at hcs1
  obtain ⟨a2, a8, a9, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27⟩ := hcs1
  -- `kalloc` cannot fail: the count is positive
  unfold kallocPost
  icases HPost with ⟨⟨%hz, Hav⟩ | ⟨%hvalid, Hbuf, Hav⟩⟩
  · obtain ⟨-, hzero⟩ := hz
    rcases hzero with h | h
    · exact absurd h (by simp)
    · injection h with h
      exact absurd hcount (by unfold kvmmakeCount kvmmakeNodes; omega)
  -- c.mv s1,a0
  k_step_gen (wp_s_add c3 _ 0x800010d0#64 true 9#5 0#5 10#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] next c4 hp4
  iintro Hk Hpc
  -- c.lui a2,0x1 ; c.li a1,0 ; jal ra, memset
  k_step_gen (wp_s_lui c4 _ 0x800010d2#64 true 1#20 12#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [km_u1] next c5 hp5
  iintro Hk Hpc
  k_step_gen (wp_s_addi c5 _ 0x800010d4#64 true 0#12 11#5 0#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] next c6 hp6
  iintro Hk Hpc
  k_step_gen (wp_s_jal c6 _ 0x800010d6#64 false 2096036#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] next c7 hp7
  iintro Hk Hpc
  iapply (km_memset_call MS c7 _ (List.replicate 4096 5#8) ?hK2 ?hn2 ?hl2) $$ [- $Hk $Hpc]
  rotate_right 1
  k_norm_g
  iframe Hbuf
  case hK2 => k_norm_g; omega
  case hn2 => k_norm_g
  case hl2 => exact List.length_replicate
  k_norm_g [km_ret_10da, km_extract0]
  iapply wpNext_intro_pin
  iintro %c8 %hp8 %R2 Hk Hpc Hbuf %hpost2
  -- the zeroed page is the root node
  have hpb : pageAddr (BitVec.extractLsb' 12 44 (R1 10#5)) = R1 10#5 :=
    Xv6.Kvm.pageAddr_of_valid _ hvalid
  ihave Hnode : nodeOwn (GF := GF) (DFrac.own 1)
      (PTree.zeroNode (BitVec.extractLsb' 12 44 (R1 10#5))) $$ [Hbuf]
  case' _ =>
    iapply (nodeOwn_of_zero_page (BitVec.extractLsb' 12 44 (R1 10#5)))
    rw [hpb]
    iexact Hbuf
  ihave Htree : ptreeOwn (GF := GF) 2 (DFrac.own 1)
      (PTree.zeroNode (BitVec.extractLsb' 12 44 (R1 10#5))) $$ [Hnode]
  case' _ =>
    iapply (ptreeOwn_zeroNode 2 (DFrac.own 1) (BitVec.extractLsb' 12 44 (R1 10#5)))
    iexact Hnode
  obtain ⟨hcs2, h10_2⟩ := hpost2
  unfold calleeSaved at hcs2
  k_norm_g at hcs2
  obtain ⟨b2, b8, b9, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27⟩ := hcs2
  have hnb : 166 < nb := by unfold kvmmakeCount kvmmakeNodes at hcount; exact hcount
  rw [show availDec (some nb) = some (nb - 1) from rfl]
  -- the six regions
  have hpin8 : k.sie = false ∨ k.proc = 0#64 → c8 = cpu := fun h =>
    (hp8 h).trans ((hp7 h).trans ((hp6 h).trans ((hp5 h).trans ((hp4 h).trans
      ((hp3 h).trans ((hp2 h).trans (hp1 h)))))))
  iapply (km_regions KM c8 _ γl γk nb (BitVec.extractLsb' 12 44 (R1 10#5)) _
    ?hnR ?hKR ?hlR hnb ?h9R ?hbvR
    iprop(frame4s1 (k.regs 2#5) (k.regs 1#5) (k.regs 8#5) (k.regs 9#5))
    iprop(wpNext k.sie k.proc cpu (kvmmakeCont k γk nb))) $$ [- $Hk $Hpc]
  rotate_right 1
  k_norm_g
  iframe #
  iframe Htree Hav Hframe
  isplitl [HΦ]
  · unfold kvmmakeCont
    iexact HΦ
  case hnR => k_norm_g; omega
  case hKR => k_norm_g; omega
  case hlR => k_norm_g; exact hlk
  case h9R => k_norm_g; exact (b9.trans hpb.symm)
  case hbvR => rw [hpb]; exact hvalid
  unfold kvmRegionsCont
  -- past the six regions
  iapply wpNext_intro_pin
  iintro %c9 %hp9 %spieR %sppR %R3 %T %hspR Hk Hpc Htree Hav Hframe HΦ %hfacts
  obtain ⟨hcsR, h9R', hsix⟩ := hfacts
  unfold calleeSaved at hcsR
  obtain ⟨r2, r8, r9, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27⟩ := hcsR
  -- c.mv a0,s1 ; jal ra, proc_mapstacks
  k_step_gen (wp_s_add c9 _ 0x8000115e#64 true 10#5 0#5 9#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [h9R'] next c10 hp10
  iintro Hk Hpc
  k_step_gen (wp_s_jal c10 _ 0x80001160#64 false 1516#21 1#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] next c11 hp11
  iintro Hk Hpc
  icases (ptreeOwn_pagesNodup' 2 _) $$ Htree with ⟨%hndS, Htree⟩
  iapply (km_mapstacks_call PM c11 _ γl γk (nb - 102) _ ?hnS ?hKS ?hlS ?hroS ?hwfS hndS ?hunmS
    ?hctS) $$ [- $Hk $Hpc]
  rotate_right 1
  k_norm_g
  iframe #
  iframe Htree Hav
  case hnS => k_norm_g; omega
  case hKS => k_norm_g; omega
  case hlS => k_norm_g; exact hlk
  case hroS => k_norm_g; exact (congrArg pageAddr hsix.2.1).symm
  case hwfS => exact hsix.1
  case hunmS => exact hsix.2.2.2.2.2.2
  case hctS =>
    refine Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_of_eq hsix.2.2.2.2.2.1) 64) ?_
    omega
  k_norm_g [km_ret_1164, km_withSpie_withSpie]
  iapply wpNext_intro_pin
  iintro %c12 %hp12 %spieS %sppS %R4 %frs %pas %hspS Hk Hpc Htree Hstack Hav %hpostS
  obtain ⟨hcsS, hleft, hlenS, hnodupS, hpgS⟩ := hpostS
  unfold calleeSaved at hcsS
  k_norm_g at hcsS
  obtain ⟨s2, s8, s9, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27⟩ := hcsS
  have hlenS0 : frs.length = 0 := hlenS.trans hsix.2.2.2.2.2.1
  rw [hlenS0]
  rw [show nb - 102 - 64 - 0 = nb - kvmmakeCount from by unfold kvmmakeCount kvmmakeNodes; omega]
  icases (ptreeOwn_pagesNodup' 2 _) $$ Htree with ⟨%hndF, Htree⟩
  have hpn : ((List.range 64).map pas).Nodup := (List.nodup_append.mp hnodupS).2.1
  have hpas : ∀ i, i < 64 → pageValid (pageAddr (pas i)) ∧ pas i ∉ T.pages 2 := fun i hi =>
    hpgS (pas i)
      (by simp only [List.mem_append, List.mem_map, List.mem_range]; exact Or.inr ⟨i, hi, rfl⟩)
  have hkt := kvmmake_table (BitVec.extractLsb' 12 44 (R1 10#5)) T _ pas frs hsix rfl hndF hpn hpas
  -- c.mv a0,s1
  k_step_gen (wp_s_add c12 _ 0x80001164#64 true 10#5 0#5 9#5 (by decide))
    from (text_instr _ _ _ _ rfl rfl) Htext $$ [- $Hk $Hpc] with [s9, h9R'] next c13 hp13
  iintro Hk Hpc
  -- the epilogue
  have hpinF : k.sie = false ∨ k.proc = 0#64 → c13 = cpu := fun h =>
    (hp13 h).trans ((hp12 h).trans ((hp11 h).trans ((hp10 h).trans ((hp9 h).trans (hpin8 h)))))
  have hspF : k.sie = false → spieS = k.spie ∧ sppS = k.spp := fun h =>
    ⟨(hspS h).1.trans ((hspR h).1.trans (hsp1 h).1),
     (hspS h).2.trans ((hspR h).2.trans (hsp1 h).2)⟩
  simp only [km_withSpie_withSpie, km_pushed_withSpie]
  have hKe : 4 ≤ (k.withSpie spieS sppS).avail := by simp only [KCtx.withSpie_avail]; omega
  have hR2e : (R4.set 10#5 (pageAddr (BitVec.extractLsb' 12 44 (R1 10#5)))) 2#5
      = (k.withSpie spieS sppS).regs 2#5 + 0xFFFFFFFFFFFFFFE0#64 := by
    simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, KCtx.withSpie_regs]
    exact s2.trans (r2.trans (b2.trans a2))
  iapply (wp_epilogue4s1_gen c13 (k.withSpie spieS sppS) 0x80001166#64 hKe
    (R4.set 10#5 (pageAddr (BitVec.extractLsb' 12 44 (R1 10#5)))) hR2e
    (k.regs 1#5) (k.regs 8#5) (k.regs 9#5)) $$ [- $Hk $Hpc]
  k_code (text_instr _ _ _ _ rfl rfl) Htext
  k_norm_g
  iframe
  inext
  ihave HΦ := wpNext_shift _ _ _ _ _ hpinF $$ HΦ
  iapply wpNext_mono _ _ _ _ _ $$ HΦ
  iintro %c14 HΦ Hk Hpc
  unfold kvmmakeCont
  iapply HΦ $$ %spieS %sppS %_ %_ %pas %hspF Hk Hpc Htree Hstack Hav
  ipureintro
  refine ⟨?_, ?_, hkt.1⟩
  · unfold calleeSaved
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true] <;>
      first
        | rfl
        | exact s18.trans (r18.trans (b18.trans a18))
        | exact s19.trans (r19.trans (b19.trans a19))
        | exact s20.trans (r20.trans (b20.trans a20))
        | exact s21.trans (r21.trans (b21.trans a21))
        | exact s22.trans (r22.trans (b22.trans a22))
        | exact s23.trans (r23.trans (b23.trans a23))
        | exact s24.trans (r24.trans (b24.trans a24))
        | exact s25.trans (r25.trans (b25.trans a25))
        | exact s26.trans (r26.trans (b26.trans a26))
        | exact s27.trans (r27.trans (b27.trans a27))
  · simp only [RegMap.set_apply, BitVec.reduceEq, ite_false, ite_true]
    exact (congrArg pageAddr hkt.2).symm
⟩

end

end Xv6
