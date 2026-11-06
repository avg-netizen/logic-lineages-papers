module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof

abbrev add {α : Type} (s t : OTerm α) : OTerm α := OrdinaryArithmetic.addTerm s t

@[simp] theorem addSubst {α β : Type} (s t : OTerm α) (ts : α → OTerm β) :
    (add s t).subst ts = add (s.subst ts) (t.subst ts) := applyTwoSubstitution _ _ _ _
@[simp] theorem liftNext {α : Type} (s : OTerm α) :
    (s.relabel Sum.inl).subst nextTerm = s.relabel Sum.inl := nextLift s
@[simp] theorem varNext {α : Type} (i : Fin 1) :
    (.var (.inr i) : OTerm (α ⊕ Fin 1)).subst nextTerm = suc (.var (.inr 0)) := rfl
@[simp] theorem impSubst {α β : Type} (p q : Formula α) (ts : α → Term β) :
    (p.imp q).subst ts = (p.subst ts).imp (q.subst ts) := rfl
@[simp] theorem impInstantiate {α : Type} (p q : Formula (α ⊕ Fin 1)) (t : Term α) :
    instantiate (p.imp q) t = (instantiate p t).imp (instantiate q t) := rfl

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def congAddLeft (s : OTerm α) {t u : OTerm α} (d : Derivation body Gamma (eqn t u)) :
    Derivation body Gamma (eqn (add s t) (add s u)) := by
  have h := congTerm (add (s.relabel Sum.inl) (.var (.inr (0 : Fin 1)))) d
  simp only [addSubst,liftBind,varBind] at h
  exact h

/-- Actual PA induction on the second addend. -/
def leftZero (t : OTerm α) : Derivation body Gamma (eqn (add z t) t) := by
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := eqn (add z x) x
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,x,eqnInstantiate,addSubst,zSubst,varBind]
    exact addZero z
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,x,successorInstance,nextEmbedding,eqnSubst,addSubst,zSubst,varNext]
    exact trans (addSucc z x) (congSuc (Derivation.hypothesis List.mem_cons_self))
  have h := Derivation.universalElimination (emb t) (natInduction theta hb hs)
  simp only [theta,x,eqnInstantiate,addSubst,zSubst,varBind] at h
  exact h

def leftSuccessor (s t : OTerm α) :
    Derivation body Gamma (eqn (add (suc s) t) (suc (add s t))) := by
  let a := s.relabel (Sum.inl : α → α ⊕ Fin 1)
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := eqn (add (suc a) x) (suc (add a x))
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,a,x,eqnInstantiate,addSubst,sucSubst,liftBind,varBind]
    exact trans (addZero (suc s)) (symm (congSuc (addZero s)))
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,a,x,successorInstance,nextEmbedding,eqnSubst,addSubst,sucSubst,liftNext,varNext]
    exact trans (addSucc (suc a) x)
      (trans (congSuc (Derivation.hypothesis List.mem_cons_self)) (symm (congSuc (addSucc a x))))
  have h := Derivation.universalElimination (emb t) (natInduction theta hb hs)
  simp only [theta,a,x,eqnInstantiate,addSubst,sucSubst,liftBind,varBind] at h
  exact h

def associativity (s t u : OTerm α) :
    Derivation body Gamma (eqn (add (add s t) u) (add s (add t u))) := by
  let a := s.relabel (Sum.inl : α → α ⊕ Fin 1)
  let b := t.relabel (Sum.inl : α → α ⊕ Fin 1)
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := eqn (add (add a b) x) (add a (add b x))
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,a,b,x,eqnInstantiate,addSubst,liftBind,varBind]
    exact trans (addZero (add s t)) (symm (congAddLeft s (addZero t)))
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,a,b,x,successorInstance,nextEmbedding,eqnSubst,addSubst,liftNext,varNext]
    exact trans (addSucc (add a b) x)
      (trans (congSuc (Derivation.hypothesis List.mem_cons_self))
        (symm (trans (congAddLeft a (addSucc b x)) (addSucc a (add b x)))))
  have h := Derivation.universalElimination (emb u) (natInduction theta hb hs)
  simp only [theta,a,b,x,eqnInstantiate,addSubst,liftBind,varBind] at h
  exact h

def rightCancellation (s t u : OTerm α) :
    Derivation body Gamma ((eqn (add s u) (add t u)).imp (eqn s t)) := by
  let a := s.relabel (Sum.inl : α → α ⊕ Fin 1)
  let b := t.relabel (Sum.inl : α → α ⊕ Fin 1)
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := (eqn (add a x) (add b x)).imp (eqn a b)
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,a,b,x,impInstantiate,eqnInstantiate,addSubst,liftBind,varBind]
    apply Derivation.implicationIntroduction
    exact trans (symm (addZero s)) (trans (Derivation.hypothesis List.mem_cons_self) (addZero t))
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,a,b,x,successorInstance,nextEmbedding,impSubst,eqnSubst,addSubst,liftNext,varNext]
    apply Derivation.implicationIntroduction
    apply Derivation.implicationElimination (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
    exact cancelSuc (trans (symm (addSucc a x))
      (trans (Derivation.hypothesis List.mem_cons_self) (addSucc b x)))
  have h := Derivation.universalElimination (emb u) (natInduction theta hb hs)
  simp only [theta,a,b,x,impInstantiate,eqnInstantiate,addSubst,liftBind,varBind] at h
  exact h

theorem actualAdditionLeftZero : InternalAdditionLawsTargets.ActualAdditionLeftZero := by
  intro body α t
  rw [onEquality]
  exact ⟨leftZero t⟩
theorem actualAdditionLeftSuccessor : InternalAdditionLawsTargets.ActualAdditionLeftSuccessor := by
  intro body α s t
  rw [onEquality]
  exact ⟨leftSuccessor s t⟩
theorem actualAdditionAssociativity : InternalAdditionLawsTargets.ActualAdditionAssociativity := by
  intro body α s t u
  rw [onEquality]
  exact ⟨associativity s t u⟩
theorem actualAdditionRightCancellation : InternalAdditionLawsTargets.ActualAdditionRightCancellation := by
  intro body α s t u
  change Nonempty (Derivation body [] ((arithmeticEmbedding.onFormula ((add s u).equal (add t u))).imp
    (arithmeticEmbedding.onFormula (s.equal t))))
  rw [onEquality,onEquality]
  exact ⟨rightCancellation s t u⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
