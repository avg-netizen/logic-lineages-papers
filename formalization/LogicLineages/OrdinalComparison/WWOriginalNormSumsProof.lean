module
public import LogicLineages.OrdinalComparison.WWOriginalNormSumsTargets
public import LogicLineages.OrdinalComparison.WWOriginalValueClosureProof
public import LogicLineages.OrdinalComparison.WWOriginalDomainProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open AdmissibleSum AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem actualNaturalSumNormAdditivity : Targets.ActualNaturalSumNormAdditivity := by
  intro a b ha hb
  obtain ⟨x, hx⟩ := normalRepresentationComplete a ha
  obtain ⟨y, hy⟩ := normalRepresentationComplete b hb
  rw [← hx, ← hy, ← naturalSumDenotation x y]
  rw [actualOrdinalNorm_notationCorrespondence (naturalSum x y),
    actualOrdinalNorm_notationCorrespondence x, actualOrdinalNorm_notationCorrespondence y]
  exact naturalSumNormAdditive x y

private theorem castAdd_eq_castLE {n m : Nat} (i : Fin n) :
    Fin.castAdd m i = Fin.castLE (Nat.le_add_right n m) i := Fin.ext rfl

theorem originalShapeNormAdditivity : Targets.OriginalShapeNormAdditivity := by
  intro Γ ρ n s xs
  induction s with
  | leaf => simp [expand, List.ofFn_succ, List.ofFn_zero]
  | @join n m a b iha ihb =>
    change actualOrdinalNorm (ordinalNaturalSum
      (expressionValue ρ (expand a (fun i => xs (Fin.castAdd m i))))
      (expressionValue ρ (expand b (fun i => xs (Fin.natAdd n i))))) = _
    rw [actualNaturalSumNormAdditivity _ _
      (originalExpressionValueBelowEpsilonZero Γ ρ _)
      (originalExpressionValueBelowEpsilonZero Γ ρ _)]
    rw [iha, ihb, List.ofFn_add, List.map_append, List.sum_append]
    simp only [castAdd_eq_castLE]

theorem originalPositiveRepeatNorm : Targets.OriginalPositiveRepeatNorm := by
  intro Γ ρ p site k t hk
  cases k with
  | zero => omega
  | succ k =>
    change actualOrdinalNorm (expressionValue ρ (expand (p.shape site k) (fun _ => t))) = _
    rw [originalShapeNormAdditivity]
    simp [List.ofFn_const, List.sum_replicate, Nat.add_mul, Nat.add_comm]

theorem originalScalarValueNorm : Targets.OriginalScalarValueNorm := by
  intro Γ ρ t ht
  obtain ⟨n, hn⟩ := originalAmbientScalarFinite Γ t ht ρ
  rw [hn, originalFiniteValueCalibration]
  exact (finiteNorm n).2

end LogicLineages.OrdinalComparison.Source.OriginalDomain
