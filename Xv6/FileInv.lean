/-
The file table's resource lemmas (a port of the parts of Rocq FileInv.v
that `filealloc` needs): opening the lock's resource and one slot, reading a
slot's `ref` cell, the ALLOC ghost step (a fresh reference id, its two
halves, the fd token parked), and the cursor arithmetic of the scan.
-/
import Xv6.FileDefs
import Xv6.PrintkDefs

namespace Xv6

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std MachCSL
open LeanRV64D

set_option linter.unusedSectionVars false

/-! ## Geometry facts -/

theorem fnode_toNat (k : Nat) (hk : k ≤ NFILE) : (fnode k).toNat = 0x800224b8 + 40 * k := by
  unfold fnode fileBase ftableAddr fileStride NFILE at *
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  omega

theorem fnode_zero : fnode 0 = 0x800224b8#64 := by
  unfold fnode fileBase ftableAddr fileStride; decide

theorem fnode_end : fnode NFILE = 0x80023458#64 := by
  unfold fnode fileBase ftableAddr fileStride NFILE; decide

theorem fnode_succ (k : Nat) : fnode k + BitVec.signExtend 64 40#12 = fnode (k + 1) := by
  unfold fnode fileStride
  have h : BitVec.signExtend 64 40#12 = 40#64 := by decide
  rw [h, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem fnode_succ' (k : Nat) : fnode k + 40#64 = fnode (k + 1) := by
  rw [← fnode_succ]; rfl

theorem fnode_ne_end (k : Nat) (hk : k < NFILE) : fnode k ≠ fnode NFILE := by
  intro e
  have h := congrArg BitVec.toNat e
  rw [fnode_toNat k (Nat.le_of_lt hk), fnode_toNat NFILE (Nat.le_refl _)] at h
  unfold NFILE at h hk; omega

theorem fnode_nonzero (k : Nat) (hk : k < NFILE) : fnode k ≠ 0#64 := by
  intro e
  have h := congrArg BitVec.toNat e
  rw [fnode_toNat k (Nat.le_of_lt hk)] at h
  simp at h

theorem aFref_eq (k : Nat) : aFref k = fnode k + BitVec.signExtend 64 4#12 := by
  unfold aFref; rfl
theorem aFref_eq' (k : Nat) : fnode k + 4#64 = aFref k := rfl

/-- The `bne s1,a4` test at the cursor. -/
theorem fa_bne_end (k : Nat) (hk : k < NFILE) :
    bcond bop.BNE (fnode k) (fnode NFILE) = true := by
  rw [bcond_bne_eq]; exact bne_iff_ne.mpr (fnode_ne_end k hk)
theorem fa_bne_end_last : bcond bop.BNE (fnode NFILE) (fnode NFILE) = false := by
  rw [bcond_bne_eq]; exact bne_self_eq_false _

/-! ## The `ref` cell's value -/

theorem fa_ref_zero : BitVec.signExtend 64 (BitVec.ofNat 32 0) = 0#64 := by decide

theorem fa_ref_nonzero (n : Nat) (hn : n ≠ 0) (hlt : n < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat 32 n) ≠ 0#64 := by
  intro e
  have h32 : BitVec.ofNat 32 n = 0#32 := by
    revert e; generalize BitVec.ofNat 32 n = x; intro e; bv_decide
  have h := congrArg BitVec.toNat h32
  simp only [BitVec.toNat_ofNat, BitVec.toNat_zero] at h
  omega

theorem fa_beqz_zero : bcond bop.BEQ (BitVec.signExtend 64 (BitVec.ofNat 32 0)) 0#64 = true := by
  decide
theorem fa_beqz_nonzero (n : Nat) (hn : n ≠ 0) (hlt : n < 2 ^ 31) :
    bcond bop.BEQ (BitVec.signExtend 64 (BitVec.ofNat 32 n)) 0#64 = false := by
  rw [bcond_beq_eq]; exact beq_eq_false_iff_ne.mpr (fa_ref_nonzero n hn hlt)

section
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [FileG GF] [CurCtx]

/-! ## Opening the table and a slot -/

theorem ftableRes_elim (γ : FileNames) (ξ : CtxId) :
    ftableResAt (GF := GF) γ ξ ⊢ ∃ (M : RegMapF (Nat × Qp)) (next : Nat),
      (γ.ref ↪●MAP M) ∗ ⌜∀ i, next ≤ i → PartialMap.get? M i = none⌝ ∗
      [∗list] k ∈ List.range NFILE, fslotAt γ ξ k := by
  unfold ftableResAt; iintro H; iexact H

theorem ftableRes_intro (γ : FileNames) (ξ : CtxId) (M : RegMapF (Nat × Qp)) (next : Nat)
    (hfresh : ∀ i, next ≤ i → PartialMap.get? M i = none) :
    (γ.ref ↪●MAP M) ∗ ([∗list] k ∈ List.range NFILE, fslotAt (GF := GF) γ ξ k) ⊢ ftableResAt γ ξ := by
  unfold ftableResAt
  iintro ⟨Ha, Hs⟩
  iexists M, next
  iframe Ha Hs
  ipureintro; exact hfresh

/-- Borrow slot `k` out of the table's big-sep. -/
theorem fslot_acc (γ : FileNames) (ξ : CtxId) (k : Nat) (hk : k < NFILE) :
    ([∗list] j ∈ List.range NFILE, fslotAt (GF := GF) γ ξ j) ⊢
      fslotAt γ ξ k ∗ (fslotAt γ ξ k -∗ [∗list] j ∈ List.range NFILE, fslotAt γ ξ j) :=
  BigSepL.bigSepL_mem_acc (List.mem_range.2 hk)

theorem fslot_elim (γ : FileNames) (ξ : CtxId) (k : Nat) :
    fslotAt (GF := GF) γ ξ k ⊢ ∃ (L : List (Nat × Qp)) (C : FContent) (pn : FPNames) (q' : Qp),
      ⌜(L.map Prod.fst).Nodup ∧ L.length < 2 ^ 31⌝ ∗
      wordAtN ξ (aFref k) 4 (DFrac.own 1) (BitVec.ofNat 32 L.length) ∗
      ([∗list] e ∈ L, frefRest γ k e) ∗ fdSlots γ L.length ∗
      ((⌜L = [] ∧ C.type = FD_NONE⌝ ∗ fileFieldsAt ξ k 1 C ∗ fpayTok γ k 1 pn ∗ fileCore 1 pn C) ∨
       (⌜L ≠ []⌝ ∗ fileRestAt γ ξ k (qsum L) q' C pn)) := by
  unfold fslotAt; iintro H; iexact H

theorem fslot_intro (γ : FileNames) (ξ : CtxId) (k : Nat) (L : List (Nat × Qp)) (C : FContent)
    (pn : FPNames) (q' : Qp) (hnd : (L.map Prod.fst).Nodup) (hlt : L.length < 2 ^ 31) :
    wordAtN (GF := GF) ξ (aFref k) 4 (DFrac.own 1) (BitVec.ofNat 32 L.length) ∗
    ([∗list] e ∈ L, frefRest γ k e) ∗ fdSlots γ L.length ∗
    ((⌜L = [] ∧ C.type = FD_NONE⌝ ∗ fileFieldsAt ξ k 1 C ∗ fpayTok γ k 1 pn ∗ fileCore 1 pn C) ∨
     (⌜L ≠ []⌝ ∗ fileRestAt γ ξ k (qsum L) q' C pn)) ⊢ fslotAt γ ξ k := by
  unfold fslotAt
  iintro ⟨H1, H2, H3, H4⟩
  iexists L, C, pn, q'
  iframe H1 H2 H3 H4
  ipureintro; exact ⟨hnd, hlt⟩

/-! ## The fd tokens -/

theorem fdSlots_zero (γ : FileNames) : ⊢ fdSlots (GF := GF) γ 0 := by
  unfold fdSlots
  iintro
  iexists []
  isplitl []
  · ipureintro; exact ⟨rfl, List.nodup_nil, fun _ h => absurd h (List.not_mem_nil)⟩
  · iapply BigSepL.bigSepL_nil.2; iempintro

/-- A whole reference element as its two halves. -/
theorem fref_halves (γ : FileNames) (id : Nat) (v : Nat × Qp) :
    (γ.ref ↪◯MAP[id] v) ⊢@{IProp GF}
      (γ.ref ↪◯MAP[id]{.own (1 : Qp).half} v) ∗ (γ.ref ↪◯MAP[id]{.own (1 : Qp).half} v) :=
by
  have h := (ghost_map_elem_fractional (GF := GF) γ.ref id v).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h.1

/-! ## THE ALLOC STEP: a free slot becomes one exclusive reference -/

/-- `file_alloc_step`: with the authority (the lock held) and the free slot's
content, mint reference `next` (fresh: nothing at or above `next` exists),
split it into the holder's half (`frefTok`) and the lock's half
(`frefRest`), park the fd token. -/
theorem file_alloc_step (γ : FileNames) (M : RegMapF (Nat × Qp)) (next k : Nat) (C : FContent)
    (pn : FPNames) (hfresh : ∀ i, next ≤ i → PartialMap.get? M i = none) (hty : C.type = FD_NONE) :
    (γ.ref ↪●MAP M) ∗ fileFieldsAt (GF := GF) curCtx k 1 C ∗ fpayTok γ k 1 pn ∗ fileCore 1 pn C ⊢
      |==> ((γ.ref ↪●MAP (PartialMap.insert M next (k, 1))) ∗
        fileRef γ k 1 .closed ∗ frefRest γ k (next, 1)) := by
  iintro ⟨Ha, Hf, Hn, Hc⟩
  ihave Hup := ghost_map_insert next (k, (1 : Qp)) (hfresh next (Nat.le_refl _)) $$ Ha
  imod Hup with ⟨Ha, He⟩
  imodintro
  iframe Ha
  ihave ⟨He1, He2⟩ := fref_halves γ next (k, (1 : Qp)) $$ He
  isplitl [He1 Hf Hn Hc]
  · unfold fileRef
    iexists C
    isplitl [He1]
    · unfold frefTok; iexists next; iexact He1
    iframe Hf
    unfold filePaySt
    iexists pn
    iframe Hn Hc
    ipureintro; exact hty
  · unfold frefRest; iexact He2

theorem qsum_single (e : Nat × Qp) : qsum [e] = e.2 := rfl

end

end Xv6
