import LogicLineages.PersistentMarking.NumberedWindowPrimitiveWitnessMarkProof

namespace LogicLineages.PersistentMarking.NumberedWindowPrimitiveWitnessReplacementProof
open NumberedWindowSyntax NumberedWindowRules NumberedWindowLiteralEquality
open NumberedWindowPrimitiveWitnessBits NumberedWindowPrimitiveWitnessTargets

theorem permutation : ExactLiteralPermutationBit := by
  intro xs ys
  letI : BEq NTerm := literalTermBEq
  letI : LawfulBEq NTerm := {
    rfl := fun {a} => (NumberedWindowLiteralEqualityProof.term a a).mpr rfl
    eq_of_beq := fun {a b} h => (NumberedWindowLiteralEqualityProof.term a b).mp h
  }
  change xs.isPerm ys = true ↔ xs.Perm ys
  exact List.isPerm_iff

theorem supplied : ExactSuppliedReplacementBit := by
  intro source target w
  have hdom : w.added.all (fun a => w.removed.any (fun b => markBit b a)) = true ↔
      ∀ a ∈ w.added, ∃ b ∈ w.removed, MarkDecrease b a := by
    simp only [List.all_eq_true,List.any_eq_true]
    constructor
    · intro h a ha
      obtain ⟨b,hb,hm⟩ := h a ha
      exact ⟨b,hb,(NumberedWindowPrimitiveWitnessMarkProof.reflection b a).mp hm⟩
    · intro h a ha
      obtain ⟨b,hb,hm⟩ := h a ha
      exact ⟨b,hb,(NumberedWindowPrimitiveWitnessMarkProof.reflection b a).mpr hm⟩
  simp only [replacementBit,Bool.and_eq_true,
    permutation source.toList (w.kept ++ w.removed),
    permutation target.toList (w.kept ++ w.added),
    Bool.not_eq_true',List.isEmpty_eq_false_iff,hdom,SuppliedReplacementMatrix,and_assoc]

theorem certified : ExactCertifiedPrimitiveReplacement := by
  intro source target
  constructor
  · rintro ⟨w,hw⟩
    exact ⟨w.kept,w.removed,w.added,(supplied source target w).mp hw⟩
  · rintro ⟨kept,removed,added,hw⟩
    exact ⟨⟨kept,removed,added⟩,(supplied source target ⟨kept,removed,added⟩).mpr hw⟩

end LogicLineages.PersistentMarking.NumberedWindowPrimitiveWitnessReplacementProof
