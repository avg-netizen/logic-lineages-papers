module

public import LogicLineages.ComputabilityKnowledge.Comparators.WWGroundClasses
public import LogicLineages.ComputabilityKnowledge.WWGroundAdmissibilityProof

@[expose] public section

/-! Original ground C-class proofs after independent target freeze. Actual
source substitution is preserved through the genuine collapse sidecondition. -/
namespace LogicLineages.ComputabilityKnowledge.WWGroundClassesProof

open PositiveExpression WWOrdinalTermSemantics WWClosedAssignment WWGroundAdmissibility WWGroundClasses

theorem sourceSubstitution : Comparators.WWGroundClasses.SourceSubstitution := by
  intro d i t ht
  induction ht with
  | one i => intro χ hχ; exact B.one i
  | omega i hi => intro χ hχ; exact B.omega i hi
  | groundVar j => intro χ hχ; exact (hχ j (Finset.mem_singleton_self j)).1
  | @add i f g hf hg ihf ihg =>
      intro χ hχ
      exact B.add (ihf χ (fun j hj => hχ j (Finset.mem_union_left _ hj)))
        (ihg χ (fun j hj => hχ j (Finset.mem_union_right _ hj)))
  | @emul i f g hi hf hg ihf ihg =>
      intro χ hχ
      exact B.emul hi (ihf χ (fun j hj => hχ j (Finset.mem_union_left _ hj)))
        (ihg χ (fun j hj => hχ j (Finset.mem_union_right _ hj)))
  | @collapse f g hf hg hside ihf ihg =>
      intro χ hχ
      exact B.collapse (ihf χ (fun j hj => hχ j (Finset.mem_union_left _ hj)))
        (ihg χ (fun j hj => hχ j (Finset.mem_union_right _ hj))) (hside χ hχ)
  | @lift i t hi ht iht =>
      intro χ hχ
      exact B.lift hi (iht χ hχ)

theorem groundFinite : Comparators.WWGroundClasses.GroundFinite := by
  intro d t ht χ hχ
  exact WWClosedAssignmentProof.originalGroundValues _ (sourceSubstitution d 0 t ht χ hχ)

theorem exactGroundExtraction : Comparators.WWGroundClasses.ExactGroundExtraction := by
  intro d t ht χ hχ
  exact WWClosedAssignmentProof.exactFiniteExtraction _ (sourceSubstitution d 0 t ht χ hχ)

theorem exponentialFragmentMembership : Comparators.WWGroundClasses.ExponentialFragmentMembership := by
  intro d e
  induction e with
  | one => intro i hi; exact C.one i
  | var j => intro i hi; exact C.lift hi (C.groundVar j)
  | add a b ha hb => intro i hi; exact C.add (ha i hi) (hb i hi)
  | emul a b ha hb => intro i hi; exact C.emul hi (ha (i + 1) (by omega)) (hb i hi)

theorem additiveFragmentMembership : Comparators.WWGroundClasses.AdditiveFragmentMembership := by
  intro d e
  induction e with
  | one => intro h; exact C.one 0
  | var j => intro h; exact C.groundVar j
  | add a b ha hb =>
      intro h
      have hab : a.depth = 0 ∧ b.depth = 0 := by simpa only [Expr.depth, Nat.max_eq_zero_iff] using h
      exact C.add (ha hab.1) (hb hab.2)
  | emul a b ha hb => intro h; simp only [Expr.depth] at h; omega

theorem wwGroundClasses : Comparators.WWGroundClasses.Target :=
  ⟨sourceSubstitution, groundFinite, exactGroundExtraction, exponentialFragmentMembership,
    additiveFragmentMembership⟩

end LogicLineages.ComputabilityKnowledge.WWGroundClassesProof
