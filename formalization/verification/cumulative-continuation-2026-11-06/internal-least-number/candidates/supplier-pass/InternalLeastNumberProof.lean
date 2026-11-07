module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalAdditionLawsProof
open InternalBetaBoundaryProof InternalQuotientComparisonProof InternalLeastNumberSyntaxProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Induction on the original additive witness, in the object calculus. -/
def additiveBoundary (s t d : OTerm α) :
    Derivation body Gamma ((eqn (add s d) t).imp (ltF s t ⊔ eqn s t)) := by
  let a := s.relabel (Sum.inl : α → α ⊕ Fin 1)
  let b := t.relabel (Sum.inl : α → α ⊕ Fin 1)
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let psi := ltF s t ⊔ eqn s t
  let theta := (eqn (add a x) b).imp (weaken psi)
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,a,b,x,impInstantiate,eqnInstantiate,addSubst,liftBind,varBind,instantiateWeaken]
    apply Derivation.implicationIntroduction
    exact orRight (trans (symm (addZero s)) (Derivation.hypothesis List.mem_cons_self))
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,a,b,x,successorInstance,nextEmbedding,impSubst,eqnSubst,addSubst,liftNext,varNext,nextWeaken]
    change Derivation body (theta :: Gamma.map weaken)
      ((eqn (add a (suc x)) b).imp ((ltF s t ⊔ eqn s t).relabel Sum.inl))
    rw [supRename,orderRename,eqnRelabel]
    apply Derivation.implicationIntroduction
    apply orLeft
    rw [embedding]
    apply Derivation.existentialIntroduction (emb x)
    rw [witnessInstantiate]
    exact Derivation.hypothesis List.mem_cons_self
  have h := Derivation.universalElimination (emb d) (natInduction theta hb hs)
  simpa only [theta,a,b,x,impInstantiate,eqnInstantiate,addSubst,liftBind,varBind,instantiateWeaken] using h

theorem actualRightSuccessorSplit : InternalLeastNumberTargets.ActualRightSuccessorSplit := by
  intro body α s t
  have h : Nonempty (Derivation body [ltF s (suc t)] (ltF s t ⊔ eqn s t)) := by
    apply orderCases [ltF s (suc t)] s (suc t) _ ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Delta d _ ⟨e⟩
    rw [supRename,orderRename,eqnRelabel]
    simp only [sucRelabel] at e
    exact ⟨Derivation.implicationElimination (additiveBoundary (s.relabel j) (t.relabel j) d)
      (cancelSuc (trans (symm (addSucc (s.relabel j) d)) e))⟩
  obtain ⟨h⟩ := h
  change Nonempty (Derivation body [] ((ltF s (suc t)).imp
    (ltF s t ⊔ arithmeticEmbedding.onFormula (s.equal t))))
  rw [onEquality]
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualNothingBelowZero : InternalLeastNumberTargets.ActualNothingBelowZero := by
  intro body α s
  have h : Nonempty (Derivation body [ltF s z] (⊥ : Formula α)) := by
    apply orderCases [ltF s z] s z _ ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Delta d _ ⟨e⟩
    simp only [zRelabel] at e
    exact ⟨Derivation.implicationElimination (sucNeZero (add (s.relabel j) d))
      (trans (symm (addSucc (s.relabel j) d)) e)⟩
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
