module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowTheoryEquality
public import LogicLineages.ComputabilityKnowledge.GorbowClosedEqualityProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowTheoryEqualityProof
open GorbowSyntax GorbowTheoryProof GorbowStandardInstances GorbowClosedEquality
open GorbowClosedEqualityProof

theorem formulaImplication : Comparators.GorbowTheoryEquality.FormulaImplication :=
  fun A φ t u p => ⟨.mp (.logical (.equalityReplace φ t u)) p⟩

theorem symmetry : Comparators.GorbowTheoryEquality.Symmetry := by
  intro A t u p
  let φ : Formula 1 := .equal (.var 0) (liftClosedTerm 1 t)
  obtain ⟨h⟩ := formulaImplication A φ t u p
  have q : Derivation A (instantiate φ t) := by
    simpa only [φ,instantiatedEqual,instantiateVariable,instantiateLift,GorbowPACore.logicalFormula] using
      (Derivation.logical (A:=A) (.reflexive t))
  have hv := Derivation.mp h q
  exact ⟨by simpa only [φ,instantiatedEqual,instantiateVariable,instantiateLift] using hv⟩

theorem transitivity : Comparators.GorbowTheoryEquality.Transitivity := by
  intro A t u v p q
  let φ : Formula 1 := .equal (liftClosedTerm 1 t) (.var 0)
  obtain ⟨h⟩ := formulaImplication A φ u v q
  have pq : Derivation A (instantiate φ u) := by
    simpa only [φ,instantiatedEqual,instantiateVariable,instantiateLift] using p
  exact ⟨by simpa only [φ,instantiatedEqual,instantiateVariable,instantiateLift] using Derivation.mp h pq⟩

theorem termCongruence : Comparators.GorbowTheoryEquality.TermCongruence := by
  intro A f t u p
  let φ : Formula 1 := .equal (liftClosedTerm 1 (instantiateTerm f t)) f
  obtain ⟨h⟩ := formulaImplication A φ t u p
  have q : Derivation A (instantiate φ t) := by
    simpa only [φ,instantiatedEqual,instantiateLift,GorbowPACore.logicalFormula] using
      (Derivation.logical (A:=A) (.reflexive (instantiateTerm f t)))
  exact ⟨by simpa only [φ,instantiatedEqual,instantiateLift] using Derivation.mp h q⟩

theorem formulaEquivalence : Comparators.GorbowTheoryEquality.FormulaEquivalence := by
  intro A φ t u p
  obtain ⟨h⟩ := formulaImplication A φ t u p
  obtain ⟨ps⟩ := symmetry A t u p
  obtain ⟨hs⟩ := formulaImplication A φ u t ps
  exact ⟨.mp (.mp (.logical (.andIntro _ _)) h) hs⟩

theorem gorbowTheoryEquality : Comparators.GorbowTheoryEquality.Target :=
  ⟨formulaImplication,symmetry,transitivity,termCongruence,formulaEquivalence⟩
end LogicLineages.ComputabilityKnowledge.GorbowTheoryEqualityProof
