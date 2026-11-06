module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionCancellationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionCancellationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- PA induction in the original calculus, not semantic reflection. -/
def commutativity (s t : OTerm α) :
    Derivation body Gamma (eqn (add s t) (add t s)) := by
  let a := s.relabel (Sum.inl : α → α ⊕ Fin 1)
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := eqn (add a x) (add x a)
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,a,x,eqnInstantiate,addSubst,liftBind,varBind]
    exact trans (addZero s) (symm (leftZero s))
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,a,x,successorInstance,nextEmbedding,eqnSubst,addSubst,liftNext,varNext]
    exact trans (addSucc a x)
      (trans (congSuc (Derivation.hypothesis List.mem_cons_self)) (symm (leftSuccessor x a)))
  have h := Derivation.universalElimination (emb t) (natInduction theta hb hs)
  simp only [theta,a,x,eqnInstantiate,addSubst,liftBind,varBind] at h
  exact h

def leftCancellation (s t u : OTerm α) :
    Derivation body Gamma ((eqn (add u s) (add u t)).imp (eqn s t)) := by
  apply Derivation.implicationIntroduction
  apply Derivation.implicationElimination (rightCancellation s t u)
  exact trans (commutativity s u)
    (trans (Derivation.hypothesis List.mem_cons_self) (commutativity u t))

theorem actualAdditionCommutativity :
    InternalAdditionCancellationTargets.ActualAdditionCommutativity := by
  intro body α s t
  rw [onEquality]
  exact ⟨commutativity s t⟩

theorem actualAdditionLeftCancellation :
    InternalAdditionCancellationTargets.ActualAdditionLeftCancellation := by
  intro body α s t u
  change Nonempty (Derivation body [] ((arithmeticEmbedding.onFormula ((add u s).equal (add u t))).imp
    (arithmeticEmbedding.onFormula (s.equal t))))
  rw [onEquality,onEquality]
  exact ⟨leftCancellation s t u⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionCancellationProof
