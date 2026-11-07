module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationCommutativityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLeftSuccessorProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationCommutativityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalMultiplicationLawsProof InternalMultiplicationLeftSuccessorProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
def multiplicationCommutativity (s t : OTerm α) :
    Derivation body Gamma (eqn (mul s t) (mul t s)) := by
  let a := s.relabel (Sum.inl : α → α ⊕ Fin 1)
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := eqn (mul a x) (mul x a)
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,a,x,eqnInstantiate,mulSubst,liftBind,varBind]
    exact trans (mulZero s) (symm (multiplicationLeftZero s))
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,a,x,successorInstance,nextEmbedding,eqnSubst,mulSubst,liftNext,varNext]
    exact trans (mulSucc a x)
      (trans (congAddRight a (Derivation.hypothesis List.mem_cons_self))
        (symm (leftSuccessorMultiplication x a)))
  have h := Derivation.universalElimination (emb t) (natInduction theta hb hs)
  simpa only [theta,a,x,eqnInstantiate,mulSubst,liftBind,varBind] using h
theorem actualMultiplicationCommutativity :
    InternalMultiplicationCommutativityTargets.ActualMultiplicationCommutativity := by
  intro body α s t
  rw [onEquality]
  exact ⟨multiplicationCommutativity s t⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationCommutativityProof
