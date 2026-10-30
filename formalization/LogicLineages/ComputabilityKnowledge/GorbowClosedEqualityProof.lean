module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowClosedEquality

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowClosedEqualityProof
open GorbowSyntax GorbowPACore GorbowStandardInstances GorbowClosedEquality

theorem closedTransport : Comparators.GorbowClosedEquality.ClosedTransport := by
  intro n t σ
  unfold liftClosedTerm
  rw [GorbowSubstitution.substitute_composition]
  have he : (fun i : Fin 0 => GorbowSubstitution.substitute σ (Fin.elim0 i : Term n))=Term.var := by
    funext i; exact Fin.elim0 i
  rw [he]
  exact GorbowSubstitution.substitute_variables t

theorem reflexivity : Comparators.GorbowClosedEquality.Reflexivity :=
  fun t => ⟨.logical (.reflexive t)⟩

theorem formulaTransport : Comparators.GorbowClosedEquality.FormulaTransport :=
  fun φ t u p q => ⟨.mp (.mp (.logical (.equalityReplace φ t u)) p) q⟩

private theorem dictionarySame (t : Term 0) :
    (show Fin 1 → Term 0 from Fin.cases t Term.var)=(show Fin 1 → Term 0 from Fin.cases t Fin.elim0) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j => exact Fin.elim0 j

theorem instantiatedEqual (f g : Term 1) (t : Term 0) :
    instantiate (.equal f g) t=.equal (instantiateTerm f t) (instantiateTerm g t) := by
  simp only [instantiate,GorbowFormulaSubstitution.substituteFormula,dictionarySame]
  rfl

theorem instantiateLift (t u : Term 0) : instantiateTerm (liftClosedTerm 1 t) u=t := by
  unfold instantiateTerm
  apply closedTransport

theorem instantiateVariable (t : Term 0) : instantiateTerm (.var 0) t=t := rfl

theorem symmetry : Comparators.GorbowClosedEquality.Symmetry := by
  intro t u p
  let φ : Formula 1 := .equal (.var 0) (liftClosedTerm 1 t)
  have q : Proof (instantiate φ t) := by
    simpa only [φ,instantiatedEqual,instantiateVariable,instantiateLift,logicalFormula] using (Proof.logical (.reflexive t))
  have h := formulaTransport φ t u p q
  simpa only [φ,instantiatedEqual,instantiateVariable,instantiateLift] using h

theorem transitivity : Comparators.GorbowClosedEquality.Transitivity := by
  intro t u v p q
  let φ : Formula 1 := .equal (liftClosedTerm 1 t) (.var 0)
  have h : Proof (instantiate φ u) := by
    simpa only [φ,instantiatedEqual,instantiateVariable,instantiateLift] using p
  have hv := formulaTransport φ u v q h
  simpa only [φ,instantiatedEqual,instantiateVariable,instantiateLift] using hv

theorem termCongruence : Comparators.GorbowClosedEquality.TermCongruence := by
  intro f t u p
  let φ : Formula 1 := .equal (liftClosedTerm 1 (instantiateTerm f t)) f
  have h : Proof (instantiate φ t) := by
    simpa only [φ,instantiatedEqual,instantiateLift,logicalFormula] using (Proof.logical (.reflexive (instantiateTerm f t)))
  have hv := formulaTransport φ t u p h
  simpa only [φ,instantiatedEqual,instantiateLift] using hv

theorem gorbowClosedEquality : Comparators.GorbowClosedEquality.Target :=
  ⟨closedTransport,reflexivity,formulaTransport,symmetry,transitivity,termCongruence⟩
end LogicLineages.ComputabilityKnowledge.GorbowClosedEqualityProof
