module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLeftSuccessorTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLawsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLeftSuccessorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalAdditionCancellationProof InternalMultiplicationLawsProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Induction on the right factor inside the original PA calculus. -/
def leftSuccessorMultiplication (s t : OTerm α) :
    Derivation body Gamma (eqn (mul (suc s) t) (add (mul s t) t)) := by
  let a := s.relabel (Sum.inl : α → α ⊕ Fin 1)
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := eqn (mul (suc a) x) (add (mul a x) x)
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,a,x,eqnInstantiate,mulSubst,addSubst,sucSubst,liftBind,varBind]
    exact trans (mulZero (suc s))
      (symm (trans (addZero (mul s z)) (mulZero s)))
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,a,x,successorInstance,nextEmbedding,eqnSubst,mulSubst,addSubst,sucSubst,liftNext,varNext]
    have rearrange : Derivation body (theta :: Gamma.map weaken)
        (eqn (add (add (mul a x) x) a) (add (add (mul a x) a) x)) :=
      trans (associativity (mul a x) x a)
        (trans (congAddLeft (mul a x) (commutativity x a))
          (symm (associativity (mul a x) a x)))
    exact trans (mulSucc (suc a) x)
      (trans (congAddRight (suc a) (Derivation.hypothesis List.mem_cons_self))
        (trans (addSucc (add (mul a x) x) a)
          (trans (congSuc rearrange)
            (symm (trans (congAddRight (suc x) (mulSucc a x))
              (addSucc (add (mul a x) a) x))))))
  have h := Derivation.universalElimination (emb t) (natInduction theta hb hs)
  simpa only [theta,a,x,eqnInstantiate,mulSubst,addSubst,sucSubst,liftBind,varBind] using h

theorem actualMultiplicationLeftSuccessor :
    InternalMultiplicationLeftSuccessorTargets.ActualMultiplicationLeftSuccessor := by
  intro body α s t
  rw [onEquality]
  exact ⟨leftSuccessorMultiplication s t⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLeftSuccessorProof
