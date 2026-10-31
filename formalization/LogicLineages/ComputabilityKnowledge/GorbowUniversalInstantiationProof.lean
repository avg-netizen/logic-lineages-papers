module

public import LogicLineages.ComputabilityKnowledge.GorbowUniversalInstantiationTargets
public import LogicLineages.ComputabilityKnowledge.GorbowClosedDeductionProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaCompositionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowUniversalInstantiation.Proof
open GorbowSyntax GorbowTheoryProof GorbowStandardInduction GorbowStandardInstances
open GorbowFormulaSubstitution

private theorem closedIdentity (phi : Formula 0) (sigma : Fin 0 → Term 0) :
    closedInstance phi sigma = phi := by
  have hs : sigma = Fin.elim0 := by funext i; exact Fin.elim0 i
  rw [closedInstance, hs]
  exact GorbowClosedDeductionProof.closedSyntax.1 phi

private theorem instantiateLift {n : Nat} (phi : Formula (n+1)) (sigma : Fin (n+1) → Term 0) :
    instantiate (substituteFormula (liftSubstitute fun i => sigma i.succ) phi) (sigma 0) =
      closedInstance phi sigma := by
  unfold instantiate closedInstance
  rw [GorbowFormulaCompositionProof.composition]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
      simp only [liftSubstitute, Fin.cases_succ, renameTerm]
      rw [GorbowSubstitution.substitute_composition]
      have he : (fun j : Fin 0 => GorbowSubstitution.substitute
          (Fin.cases (sigma 0) Term.var) (Term.var j.succ)) = Term.var := by
        funext j
        exact Fin.elim0 j
      rw [he]
      exact GorbowSubstitution.substitute_variables (sigma i.succ)

theorem universalSpecialization : Targets.UniversalSpecialization := by
  intro A n
  induction n with
  | zero =>
      intro phi sigma p
      rw [closedIdentity]
      exact ⟨p⟩
  | succ n ih =>
      intro phi sigma p
      obtain ⟨q⟩ := ih (.all phi) (fun i => sigma i.succ) p
      change Derivation A (.all (substituteFormula (liftSubstitute fun i => sigma i.succ) phi)) at q
      have r := Derivation.mp (Derivation.logical (A:=A)
        (.allInstantiate (substituteFormula (liftSubstitute fun i => sigma i.succ) phi) (sigma 0))) q
      exact ⟨by simpa only [instantiateLift] using r⟩

theorem axiomSpecialization : Targets.AxiomSpecialization := by
  intro A n phi sigma h
  have p : Derivation A (universalClosure phi) := by
    simpa only [GorbowClosedDeductionProof.closedSyntax.1] using
      (Derivation.axiom (A:=A) (n:=0) (universalClosure phi) h)
  exact universalSpecialization A n phi sigma p

end LogicLineages.ComputabilityKnowledge.GorbowUniversalInstantiation.Proof
