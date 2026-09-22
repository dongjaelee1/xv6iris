/-
The "nothing outside the window touched" relation between two user-memory
images: what a byte-at-a-time `copyout` loop (piperead) leaves behind.  Its
positions are taken modulo `2^64` (`(a + i).toNat`), as the loop's `addr++`
does; the run's bytes stay existential (they come out of the pipe).
-/
import Xv6.UMemLemmas

namespace Xv6.UMemL

/-- `M'` agrees with `M0` everywhere but on `[a, a + d)`, page lengths kept. -/
def umemUntouched (M0 M' : Nat → List (BitVec 8)) (a : BitVec 64) (d : Nat) : Prop :=
  (∀ k, (M' k).length = (M0 k).length) ∧
  ∀ k j, (∀ i, i < d → k * 4096 + j ≠ (a + BitVec.ofNat 64 i).toNat) → (M' k)[j]? = (M0 k)[j]?

theorem umemUntouched_refl (M0 : Nat → List (BitVec 8)) (a : BitVec 64) : umemUntouched M0 M0 a 0 :=
  ⟨fun _ => rfl, fun _ _ _ => rfl⟩

/-- One more byte written at the window's end. -/
theorem umemUntouched_write (M0 M' : Nat → List (BitVec 8)) (a : BitVec 64) (d : Nat) (b : BitVec 8)
    (h : umemUntouched M0 M' a d) :
    umemUntouched M0 (umemWrite M' (a + BitVec.ofNat 64 d).toNat [b]) a (d + 1) := by
  obtain ⟨hl, hv⟩ := h
  refine ⟨fun k => by rw [umemWrite_length]; exact hl k, fun k j hout => ?_⟩
  rw [umemWrite_getElem?]
  have hne : k * 4096 + j ≠ (a + BitVec.ofNat 64 d).toNat := hout d (by omega)
  have hout' : ∀ i, i < d → k * 4096 + j ≠ (a + BitVec.ofNat 64 i).toNat :=
    fun i hi => hout i (by omega)
  rw [← hv k j hout']
  simp only [List.length_singleton]
  cases (M' k)[j]? with
  | none => rfl
  | some x =>
    simp only [Option.map_some, Option.some.injEq]
    rw [if_neg]
    omega

/-- Per page, a later extension either leaves both views alone or zeroes both. -/
theorem viewFaulted_step {P P' P'' : UPtd} (M M' : Nat → List (BitVec 8))
    (hext : P.ext P') (hext' : P'.ext P'') (k : Nat) :
    (viewFaulted P P'' M k = viewFaulted P P' M k ∧ viewFaulted P' P'' M' k = M' k) ∨
    (viewFaulted P P'' M k = List.replicate 4096 0#8 ∧
      viewFaulted P' P'' M' k = List.replicate 4096 0#8) := by
  obtain ⟨-, -, hsub⟩ := hext
  obtain ⟨-, -, hsub'⟩ := hext'
  unfold viewFaulted
  cases h0 : Iris.Std.PartialMap.get? P.um k with
  | some w =>
    have h1 := hsub k w h0
    have h2 := hsub' k w h1
    simp only [h0, h1, h2, Option.isNone_some, Option.isNone_none, Option.isSome_some,
      Option.isSome_none, Bool.false_eq_true, eq_self_iff_true, and_false, false_and, and_true,
      true_and, ite_true, ite_false, true_or, or_true]
  | none =>
    cases h1 : Iris.Std.PartialMap.get? P'.um k with
    | some w =>
      have h2 := hsub' k w h1
      simp only [h0, h1, h2, Option.isNone_some, Option.isNone_none, Option.isSome_some,
        Option.isSome_none, Bool.false_eq_true, eq_self_iff_true, and_false, false_and, and_true,
        true_and, ite_true, ite_false, true_or, or_true]
    | none =>
      cases h2 : Iris.Std.PartialMap.get? P''.um k with
      | some w =>
        simp only [h0, h1, h2, Option.isNone_some, Option.isNone_none, Option.isSome_some,
          Option.isSome_none, Bool.false_eq_true, eq_self_iff_true, and_false, false_and, and_true,
          true_and, ite_true, ite_false, true_or, or_true]
      | none =>
        simp only [h0, h1, h2, Option.isNone_some, Option.isNone_none, Option.isSome_some,
          Option.isSome_none, Bool.false_eq_true, eq_self_iff_true, and_false, false_and, and_true,
          true_and, ite_true, ite_false, true_or, or_true]

/-- The base image extended again (later lazy faults): the untouched part
follows (`viewFaulted` zeroes only pages new to the later table, which the
earlier image never held). -/
theorem umemUntouched_view {P P' P'' : UPtd} (M M' : Nat → List (BitVec 8)) (a : BitVec 64) (d : Nat)
    (hext : P.ext P') (hext' : P'.ext P'')
    (h : umemUntouched (viewFaulted P P' M) M' a d) :
    umemUntouched (viewFaulted P P'' M) (viewFaulted P' P'' M') a d := by
  obtain ⟨hl, hv⟩ := h
  refine ⟨fun k => ?_, fun k j hout => ?_⟩
  · rcases viewFaulted_step M M' hext hext' k with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]; exact hl k
    · rw [e1, e2]
  · rcases viewFaulted_step M M' hext hext' k with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]; exact hv k j hout
    · rw [e1, e2]

end Xv6.UMemL
