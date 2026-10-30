module

public import LogicLineages.ComputabilityKnowledge.Comparators.WWGroundAdmissibility
public import LogicLineages.ComputabilityKnowledge.WWClosedAssignmentProof

@[expose] public section

/-! Source ground-domain proof after independent target freeze. Substitutions
are constrained only on actual occurring names; the total function notation
introduces no extra admissibility restriction. -/
namespace LogicLineages.ComputabilityKnowledge.WWGroundAdmissibilityProof

open PositiveExpression WWOrdinalTermSemantics WWClosedAssignment WWGroundAdmissibility
open LogicLineages.OrdinalComparison

theorem originalLocality : Comparators.WWGroundAdmissibility.OriginalLocality := by
  intro d a ρ σ h
  induction a with
  | var i => exact h i (Finset.mem_singleton_self i)
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add a b ha hb =>
      simp only [denote]
      rw [ha (fun i hi => h i (Finset.mem_union_left _ hi)),
        hb (fun i hi => h i (Finset.mem_union_right _ hi))]
  | emul a b ha hb =>
      simp only [denote]
      rw [ha (fun i hi => h i (Finset.mem_union_left _ hi)),
        hb (fun i hi => h i (Finset.mem_union_right _ hi))]
  | collapse a b ha hb =>
      simp only [denote]
      rw [ha (fun i hi => h i (Finset.mem_union_left _ hi)),
        hb (fun i hi => h i (Finset.mem_union_right _ hi))]

theorem restrictionExtension : Comparators.WWGroundAdmissibility.RestrictionExtension := by
  intro d S χ h
  constructor
  · intro i hi
    by_cases hs : i ∈ S
    · simpa only [hs, ↓reduceIte] using h i hs
    · simp only [hs, ↓reduceIte]
      exact ⟨B.one 0, WWClosedAssignmentProof.singletonBoundedNorm _⟩
  · intro i hi
    simp only [hi, ↓reduceIte]

theorem exactPositiveTuples : Comparators.WWGroundAdmissibility.ExactPositiveTuples := by
  classical
  constructor
  · intro d S χ h
    let ρ : Fin d → PosNat := fun i => if hi : i ∈ S then
      ⟨(closedValue (χ i)).card.toNat,
        (WWClosedAssignmentProof.exactFiniteExtraction (χ i) (h i hi).1).1⟩ else ⟨1, by decide⟩
    refine ⟨ρ, ?_⟩
    intro i hi
    simp only [ρ, hi, ↓reduceDIte]
    exact (WWClosedAssignmentProof.exactFiniteExtraction (χ i) (h i hi).1).2.1.symm
  · intro d ρ
    let χ : Fin d → Term Empty := fun i => positiveNumeral ((ρ i : Nat) - 1)
    refine ⟨χ, ?_, ?_⟩
    · intro i hi
      exact ⟨(WWClosedAssignmentProof.literalPositiveRepresentatives _).1,
        WWClosedAssignmentProof.singletonBoundedNorm _⟩
    · intro i
      change closedValue (positiveNumeral _) = _
      rw [(WWClosedAssignmentProof.literalPositiveRepresentatives _).2,
        Nat.sub_add_cancel (ρ i).property]

private theorem substituted_embedding (d : Nat) (e : Expr (Fin d))
    (χ : Fin d → Term Empty) (ρ : Fin d → PosNat)
    (h : ∀ i ∈ support (embed e), closedValue (χ i) = ((ρ i : Nat) : Ordinal.{0})) :
    closedValue (substitute χ (embed e)) = (e.eval ρ : Ordinal.{0}) := by
  unfold closedValue
  rw [WWOrdinalTermSemanticsProof.structuralSubstitution]
  exact (originalLocality d (embed e) _ _ h).trans
    (WWOrdinalTermSemanticsProof.literalEmbedding d e ρ).1

private theorem pair_values (d : Nat) (a b : Expr (Fin d)) (χ : Fin d → Term Empty)
    (ρ : Fin d → PosNat)
    (h : ∀ i ∈ support (embed a) ∪ support (embed b),
      closedValue (χ i) = ((ρ i : Nat) : Ordinal.{0})) :
    closedValue (substitute χ (embed a)) = (a.eval ρ : Ordinal.{0}) ∧
      closedValue (substitute χ (embed b)) = (b.eval ρ : Ordinal.{0}) :=
  ⟨substituted_embedding d a χ ρ (fun i hi => h i (Finset.mem_union_left _ hi)),
    substituted_embedding d b χ ρ (fun i hi => h i (Finset.mem_union_right _ hi))⟩

theorem sourceComparisons : Comparators.WWGroundAdmissibility.SourceComparisons := by
  intro d a b weak
  constructor
  · intro h ρ
    obtain ⟨χ, hχ, hρ⟩ := exactPositiveTuples.2 d ρ
    have hh := h χ (fun i hi => hχ i (Finset.mem_univ i))
    obtain ⟨ha, hb⟩ := pair_values d a b χ ρ (fun i hi => hρ i)
    cases weak <;> simpa only [Bool.false_eq_true, ↓reduceIte, ha, hb, Nat.cast_lt,
      Nat.cast_le] using hh
  · intro h χ hχ
    obtain ⟨ρ, hρ⟩ := exactPositiveTuples.1 d _ χ hχ
    obtain ⟨ha, hb⟩ := pair_values d a b χ ρ hρ
    have hh := h ρ
    cases weak <;> simpa only [Bool.false_eq_true, ↓reduceIte, ha, hb, Nat.cast_lt,
      Nat.cast_le] using hh

theorem sourceEquality : Comparators.WWGroundAdmissibility.SourceEquality := by
  intro d a b
  constructor
  · intro h ρ
    obtain ⟨χ, hχ, hρ⟩ := exactPositiveTuples.2 d ρ
    have hh := h χ (fun i hi => hχ i (Finset.mem_univ i))
    obtain ⟨ha, hb⟩ := pair_values d a b χ ρ (fun i hi => hρ i)
    rw [ha, hb] at hh
    exact_mod_cast hh
  · intro h χ hχ
    obtain ⟨ρ, hρ⟩ := exactPositiveTuples.1 d _ χ hχ
    obtain ⟨ha, hb⟩ := pair_values d a b χ ρ hρ
    rw [ha, hb, h ρ]

theorem sourceNormComparisons : Comparators.WWGroundAdmissibility.SourceNormComparisons := by
  intro d a b weak
  constructor
  · intro h ρ
    obtain ⟨χ, hχ, hρ⟩ := exactPositiveTuples.2 d ρ
    have hh := h χ (fun i hi => hχ i (Finset.mem_univ i))
    obtain ⟨ha, hb⟩ := pair_values d a b χ ρ (fun i hi => hρ i)
    cases weak <;> simpa only [Bool.false_eq_true, ↓reduceIte, ha, hb,
      (WWOrdinalTermSemanticsProof.finiteNorm _).2] using hh
  · intro h χ hχ
    obtain ⟨ρ, hρ⟩ := exactPositiveTuples.1 d _ χ hχ
    obtain ⟨ha, hb⟩ := pair_values d a b χ ρ hρ
    have hh := h ρ
    cases weak <;> simpa only [Bool.false_eq_true, ↓reduceIte, ha, hb,
      (WWOrdinalTermSemanticsProof.finiteNorm _).2] using hh

theorem wwGroundAdmissibility : Comparators.WWGroundAdmissibility.Target :=
  ⟨originalLocality, restrictionExtension, exactPositiveTuples, sourceComparisons,
    sourceEquality, sourceNormComparisons⟩

end LogicLineages.ComputabilityKnowledge.WWGroundAdmissibilityProof
