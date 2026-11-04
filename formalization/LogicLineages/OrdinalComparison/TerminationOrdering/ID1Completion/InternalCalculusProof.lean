module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticSchemas
open SourceComputabilityFormulaSupportProof PositiveArithmeticSchemasProof
open InternalCalculus InternalCalculusSupportProof

theorem actualInternalInvariantInduction : InternalCalculusTargets.ActualInternalInvariantInduction := by
  intro body α Gamma theta ⟨step⟩
  exact ⟨Derivation.implicationElimination (Derivation.inductiveLeastness theta)
    (Derivation.universalIntroduction (Derivation.implicationIntroduction step))⟩

theorem actualInternalNaturalInduction : InternalCalculusTargets.ActualInternalNaturalInduction := by
  intro body α Gamma theta ⟨base⟩ ⟨step⟩
  exact ⟨Derivation.implicationElimination (Derivation.arithmetic (.induction theta))
    (Derivation.conjunctionIntroduction base
      (Derivation.universalIntroduction (Derivation.implicationIntroduction step)))⟩

theorem actualInternalInvariantInstance : InternalCalculusTargets.ActualInternalInvariantInstance := by
  intro body α Gamma theta t hstep
  obtain ⟨h⟩ := actualInternalInvariantInduction body α Gamma theta hstep
  exact ⟨Derivation.universalElimination t h⟩

theorem actualInternalCalculusSoundness : InternalCalculusTargets.ActualInternalCalculusSoundness := by
  intro body P hmodel α Gamma phi ⟨d⟩
  letI := naturalStructure P
  induction d with
  | hypothesis h =>
    intro v hv
    exact hv _ h
  | weakening h d ih =>
    intro v hv
    exact ih v (fun p hp => hv p (h p hp))
  | implicationIntroduction d ih =>
    intro v hv
    rw [generalImpTruth]
    intro hphi
    apply ih v
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hphi
    · exact hv p hp
  | implicationElimination d e ihd ihe =>
    intro v hv
    exact (generalImpTruth _ _ _ _).mp (ihd v hv) (ihe v hv)
  | conjunctionIntroduction d e ihd ihe =>
    intro v hv
    exact (generalConjTruth _ _ _ _).mpr ⟨ihd v hv,ihe v hv⟩
  | conjunctionLeft d ih =>
    intro v hv
    exact ((generalConjTruth _ _ _ _).mp (ih v hv)).1
  | conjunctionRight d ih =>
    intro v hv
    exact ((generalConjTruth _ _ _ _).mp (ih v hv)).2
  | explosion d ih =>
    intro v hv
    exact False.elim (ih v hv)
  | classical d ih =>
    intro v hv
    apply Classical.byContradiction
    intro hnot
    apply ih v
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hnot
    · exact hv p hp
  | universalIntroduction d ih =>
    intro v hv
    rw [allScalarTruth]
    intro x
    apply ih (Sum.elim v (fun _ => x))
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact (weakenTruth q P v x).mpr (hv q hq)
  | universalElimination t d ih =>
    intro v hv
    exact (instantiateTruth _ t P v).mpr ((allScalarTruth _ P v).mp (ih v hv) (t.realize v))
  | existentialIntroduction t d ih =>
    intro v hv
    exact (existsScalarTruth _ P v).mpr ⟨t.realize v,(instantiateTruth _ t P v).mp (ih v hv)⟩
  | existentialElimination d e ihd ihe =>
    intro v hv
    obtain ⟨x,hx⟩ := (existsScalarTruth _ P v).mp (ihd v hv)
    apply (weakenTruth _ P v x).mp
    apply ihe (Sum.elim v (fun _ => x))
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hx
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      exact (weakenTruth q P v x).mpr (hv q hq)
  | equalityReflexivity t =>
    intro v hv
    exact (FirstOrder.Language.Formula.realize_equal).mpr rfl
  | equalityElimination theta t u d e ihd ihe =>
    intro v hv
    have he : t.realize v = u.realize v := (FirstOrder.Language.Formula.realize_equal).mp (ihd v hv)
    apply (instantiateTruth theta u P v).mpr
    rw [← he]
    exact (instantiateTruth theta t P v).mp (ihe v hv)
  | arithmetic w =>
    intro v hv
    exact arithmeticTruth w P v
  | inductiveClosure =>
    intro v hv
    exact hmodel.1 _ v
  | inductiveLeastness theta =>
    intro v hv
    exact hmodel.2 _ theta v

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusProof
