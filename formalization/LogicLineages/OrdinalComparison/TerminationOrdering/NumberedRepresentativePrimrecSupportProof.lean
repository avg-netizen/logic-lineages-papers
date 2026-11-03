module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentativePrimrecTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentativePrimrecSupportProof
open Source NumberedRewriteReduction NumberedFinitePrimaryClass
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedRepresentativePrimrec

local instance {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} :
    DecidableEq (Packed (Fin n) arity Gamma) :=
  NumberedAuxiliaryCodingProof.packedDecidableEq

theorem classNumberTestCorrect {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (symbols : List (Fin n)) (S : List Ty) (q : Packed (Fin n) arity Gamma)
    (value : Nat) :
    classNumberTest symbols S q value = true ↔ value ∈ classNumbers symbols S q := by
  constructor
  · intro h
    cases hd : decodePackedNumber n arity Gamma value with
    | none => simp [classNumberTest, hd] at h
    | some r =>
      have hr : r ∈ primaryClass symbols S q := by
        simpa [classNumberTest, hd, primaryTest] using h
      exact Finset.mem_image.mpr
        ⟨r, hr, NumberedNumericDecodingProof.packedNumericSound n arity Gamma value r hd⟩
  · intro h
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp h
    have hd : decodePackedNumber n arity Gamma value = some r := by
      rw [← he]
      exact NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma r
    simpa [classNumberTest, hd, primaryTest] using hr

theorem representativeBound : NumberedRepresentativePrimrecTargets.ActualRepresentativeBound := by
  intro n arity Gamma symbols S q
  exact Finset.min'_le _ _ (Finset.mem_image.mpr
    ⟨q, NumberedFinitePrimaryClassProof.initialMember symbols S q _, rfl⟩)

theorem boundedRepresentativeCalibration :
    NumberedRepresentativePrimrecTargets.ActualBoundedRepresentativeCalibration := by
  intro n arity Gamma symbols S q
  have hlt : representativeCode symbols S q < (List.range (packedNumber q + 1)).length := by
    simpa only [List.length_range] using
      Nat.lt_succ_of_le (representativeBound n arity Gamma symbols S q)
  unfold boundedRepresentative
  apply (List.findIdx_eq hlt).mpr
  constructor
  · simpa only [List.getElem_range] using
      (classNumberTestCorrect symbols S q (representativeCode symbols S q)).mpr
        (Finset.min'_mem (classNumbers symbols S q) (classNumbersNonempty symbols S q))
  · intro j hj
    simp only [List.getElem_range]
    cases ht : classNumberTest symbols S q j with
    | false => rfl
    | true =>
      have hm := (classNumberTestCorrect symbols S q j).mp ht
      have hle : representativeCode symbols S q ≤ j := Finset.min'_le _ _ hm
      exact False.elim (Nat.not_le_of_lt hj hle)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentativePrimrecSupportProof
