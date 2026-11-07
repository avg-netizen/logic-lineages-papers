module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalQuotientComparison InternalQuotientComparisonSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalAdditionLawsProof
open InternalBetaBoundaryProof InternalBetaTotalityProof InternalPositiveUnfoldingSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def orLeft {p q : Formula α} (d : Derivation body Gamma p) :
    Derivation body Gamma (p ⊔ q) :=
  Derivation.implicationIntroduction (Derivation.explosion
    (Derivation.implicationElimination (Derivation.hypothesis List.mem_cons_self) (addHyp d p.not)))

def orRight {p q : Formula α} (d : Derivation body Gamma q) :
    Derivation body Gamma (p ⊔ q) :=
  Derivation.implicationIntroduction (addHyp d p.not)

theorem comparisonEmbedding (s t : OrdinaryArithmetic.Term α) :
    comparison s t = ltF s t ⊔ (eqn s t ⊔ ltF t s) := by
  unfold comparison
  rw [onEquality]
  rfl

def compareLeft {s t : OrdinaryArithmetic.Term α} (d : Derivation body Gamma (ltF s t)) :
    Derivation body Gamma (comparison s t) := by
  rw [comparisonEmbedding]
  exact orLeft d
def compareEqual {s t : OrdinaryArithmetic.Term α} (d : Derivation body Gamma (eqn s t)) :
    Derivation body Gamma (comparison s t) := by
  rw [comparisonEmbedding]
  exact orRight (orLeft d)
def compareRight {s t : OrdinaryArithmetic.Term α} (d : Derivation body Gamma (ltF t s)) :
    Derivation body Gamma (comparison s t) := by
  rw [comparisonEmbedding]
  exact orRight (orRight d)
def compareView {s t : OrdinaryArithmetic.Term α} (d : Derivation body Gamma (comparison s t)) :
    Derivation body Gamma (ltF s t ⊔ (eqn s t ⊔ ltF t s)) := by
  rw [← comparisonEmbedding]
  exact d

def zeroLessSuccessor (s : OrdinaryArithmetic.Term α) : Derivation body Gamma (ltF z (suc s)) := by
  rw [embedding]
  apply Derivation.existentialIntroduction (emb s)
  rw [witnessInstantiate]
  exact leftZero (suc s)

def equalToNext {s t : OrdinaryArithmetic.Term α} (e : Derivation body Gamma (eqn s t)) :
    Derivation body Gamma (ltF s (suc t)) := by
  rw [embedding]
  apply Derivation.existentialIntroduction (emb z)
  rw [witnessInstantiate]
  exact trans (addSucc s z) (trans (congSuc (addZero s)) (congSuc e))

def comparisonZero (s : OrdinaryArithmetic.Term α) : Derivation body Gamma (comparison s z) := by
  let x : OrdinaryArithmetic.Term (α ⊕ Fin 1) := .var (.inr 0)
  let theta := comparison x z
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,x,comparisonInstantiate,varBind,zSubst]
    exact compareEqual (refl z)
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,x,comparisonSuccessor,varNext,zSubst]
    exact compareRight (zeroLessSuccessor x)
  have h := Derivation.universalElimination (emb s) (natInduction theta hb hs)
  simpa only [theta,x,comparisonInstantiate,varBind,zSubst] using h

theorem actualRightSuccessorOrder : InternalQuotientComparisonTargets.ActualRightSuccessorOrder := by
  intro body α s t
  have h : Nonempty (Derivation body [ltF s t] (ltF s (suc t))) := by
    apply orderCases [ltF s t] s t _ ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Delta d _ ⟨e⟩
    rw [orderRename,sucRelabel]
    apply actualOriginalOrderIntroduction body β Delta (s.relabel j) (suc (t.relabel j)) (suc d)
    rw [onEquality]
    exact ⟨trans (addSucc (s.relabel j) (suc d)) (congSuc e)⟩
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationIntroduction h⟩

theorem comparisonStep (body : Positive (Fin 1)) (α : Type) (s t : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body [] ((comparison s t).imp (comparison s (suc t)))) := by
  obtain ⟨forward⟩ := actualRightSuccessorOrder body α s t
  obtain ⟨boundary⟩ := actualDiscreteOrderBoundary body α t s
  change Derivation body [] ((ltF t s).imp
    (ltF (suc t) s ⊔ arithmeticEmbedding.onFormula ((suc t).equal s))) at boundary
  rw [onEquality] at boundary
  let Gamma := [comparison s t]
  let p := ltF s t
  let q := eqn s t
  let r := ltF t s
  let c := comparison s (suc t)
  have hp : Derivation body Gamma (p.imp c) :=
    Derivation.implicationIntroduction (compareLeft
      (Derivation.implicationElimination (weakenClosed forward (p :: Gamma))
        (Derivation.hypothesis List.mem_cons_self)))
  have hq : Derivation body Gamma (q.imp c) :=
    Derivation.implicationIntroduction (compareLeft
      (equalToNext (Derivation.hypothesis List.mem_cons_self)))
  have hr : Derivation body Gamma (r.imp c) := by
    apply Derivation.implicationIntroduction
    have bd : Derivation body (r :: Gamma) (ltF (suc t) s ⊔ eqn (suc t) s) :=
      Derivation.implicationElimination (weakenClosed boundary (r :: Gamma))
        (Derivation.hypothesis List.mem_cons_self)
    exact disjunctionElimination bd
      (Derivation.implicationIntroduction (compareRight (Derivation.hypothesis List.mem_cons_self)))
      (Derivation.implicationIntroduction (compareEqual (symm (Derivation.hypothesis List.mem_cons_self))))
  have hqr : Derivation body Gamma ((q ⊔ r).imp c) :=
    Derivation.implicationIntroduction (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp hq (q ⊔ r)) (addHyp hr (q ⊔ r)))
  have hc : Derivation body Gamma (p ⊔ (q ⊔ r)) :=
    compareView (Derivation.hypothesis List.mem_cons_self)
  exact ⟨Derivation.implicationIntroduction (disjunctionElimination hc hp hqr)⟩

theorem actualOriginalComparison : InternalQuotientComparisonTargets.ActualOriginalComparison := by
  intro body α s t
  let a := s.relabel (Sum.inl : α → α ⊕ Fin 1)
  let x : OrdinaryArithmetic.Term (α ⊕ Fin 1) := .var (.inr 0)
  let theta := comparison a x
  have hb : Derivation body [] (instantiate theta (emb z)) := by
    simp only [theta,a,x,comparisonInstantiate,liftBind,varBind]
    exact comparisonZero s
  have hs : Nonempty (Derivation body [theta] (successorInstance theta)) := by
    simp only [theta,a,x,comparisonSuccessor,liftNext,varNext]
    obtain ⟨step⟩ := comparisonStep body (α ⊕ Fin 1) a x
    exact ⟨Derivation.implicationElimination (weakenClosed step [theta])
      (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb t) (natInduction theta hb hs)
  simpa only [theta,a,x,comparisonInstantiate,liftBind,varBind] using (Nonempty.intro h)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
