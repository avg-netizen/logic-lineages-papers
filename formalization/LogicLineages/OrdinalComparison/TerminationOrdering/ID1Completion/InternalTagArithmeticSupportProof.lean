module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms
open SourceComputabilityFormulaSupportProof
open InternalCalculus InternalSourceInversionSupportProof InternalTagArithmeticSyntaxProof
open InternalPositiveUnfoldingSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def refl (s : OTerm α) : Derivation body Gamma (eqn s s) := Derivation.equalityReflexivity (emb s)
def symm {s t : OTerm α} (d : Derivation body Gamma (eqn s t)) : Derivation body Gamma (eqn t s) := by
  have h := Derivation.equalityElimination (eqn (.var (.inr 0)) (s.relabel Sum.inl)) (emb s) (emb t) d
  simp only [eqnInstantiate,varBind,liftBind] at h
  exact h (refl s)
def trans {s t u : OTerm α} (d : Derivation body Gamma (eqn s t))
    (e : Derivation body Gamma (eqn t u)) : Derivation body Gamma (eqn s u) := by
  have h := Derivation.equalityElimination (eqn (s.relabel Sum.inl) (.var (.inr 0))) (emb t) (emb u) e
  simp only [eqnInstantiate,varBind,liftBind] at h
  exact h d

def congTerm (f : OTerm (α ⊕ Fin 1)) {s t : OTerm α} (d : Derivation body Gamma (eqn s t)) :
    Derivation body Gamma (eqn (f.subst (bindTerm s)) (f.subst (bindTerm t))) := by
  have h := Derivation.equalityElimination (eqn ((f.subst (bindTerm s)).relabel Sum.inl) f) (emb s) (emb t) d
  simp only [eqnInstantiate,liftBind] at h
  exact h (refl _)
def congSuc {s t : OTerm α} (d : Derivation body Gamma (eqn s t)) :
    Derivation body Gamma (eqn (suc s) (suc t)) := by
  have h := congTerm (suc (.var (.inr 0))) d
  simpa only [sucSubst,varBind] using h

def cancelSuc {s t : OTerm α} (d : Derivation body Gamma (eqn (suc s) (suc t))) :
    Derivation body Gamma (eqn s t) := by
  have h := Derivation.arithmetic (body := body) (Gamma := Gamma) (.successorInjective s t)
  change Derivation body Gamma ((arithmeticEmbedding.onFormula ((suc s).equal (suc t))).imp
    (arithmeticEmbedding.onFormula (s.equal t))) at h
  simp only [onEquality] at h
  exact Derivation.implicationElimination h d

def sucNeZero (s : OTerm α) : Derivation body Gamma (eqn (suc s) z).not := by
  have h := Derivation.arithmetic (body := body) (Gamma := Gamma) (.successorNotZero s)
  change Derivation body Gamma (arithmeticEmbedding.onFormula ((suc s).equal z)).not at h
  rw [onEquality] at h
  exact h

def zeroNeSuc {s : OTerm α} (d : Derivation body Gamma (eqn z (suc s))) : Derivation body Gamma ⊥ :=
  Derivation.implicationElimination (sucNeZero s) (symm d)
def sucNeZeroApply {s : OTerm α} (d : Derivation body Gamma (eqn (suc s) z)) : Derivation body Gamma ⊥ :=
  Derivation.implicationElimination (sucNeZero s) d

def doubleZero : Derivation body Gamma (eqn (dbl (z : OTerm α)) z) := by
  have h := Derivation.arithmetic (body := body) (Gamma := Gamma) (.multiplicationZero (suc (suc z)))
  change Derivation body Gamma (arithmeticEmbedding.onFormula ((dbl (z : OTerm α)).equal z)) at h
  rw [onEquality] at h
  exact h

def addZero (s : OTerm α) : Derivation body Gamma (eqn (OrdinaryArithmetic.addTerm s z) s) := by
  have h := Derivation.arithmetic (body := body) (Gamma := Gamma) (.additionZero s)
  change Derivation body Gamma (arithmeticEmbedding.onFormula ((OrdinaryArithmetic.addTerm s z).equal s)) at h
  rw [onEquality] at h
  exact h

def addSucc (s t : OTerm α) : Derivation body Gamma
    (eqn (OrdinaryArithmetic.addTerm s (suc t)) (suc (OrdinaryArithmetic.addTerm s t))) := by
  have h := Derivation.arithmetic (body := body) (Gamma := Gamma) (.additionSuccessor s t)
  change Derivation body Gamma (arithmeticEmbedding.onFormula
    ((OrdinaryArithmetic.addTerm s (suc t)).equal (suc (OrdinaryArithmetic.addTerm s t)))) at h
  rw [onEquality] at h
  exact h

def doubleSucc (s : OTerm α) : Derivation body Gamma (eqn (dbl (suc s)) (suc (suc (dbl s)))) := by
  have h := Derivation.arithmetic (body := body) (Gamma := Gamma) (.multiplicationSuccessor (suc (suc z)) s)
  change Derivation body Gamma (arithmeticEmbedding.onFormula
    ((dbl (suc s)).equal (OrdinaryArithmetic.addTerm (dbl s) (suc (suc z))))) at h
  rw [onEquality] at h
  exact trans h (trans (addSucc (dbl s) (suc z))
    (congSuc (trans (addSucc (dbl s) z) (congSuc (addZero (dbl s))))))

def align {s s' t t' : OTerm α} (ds : Derivation body Gamma (eqn s s'))
    (dt : Derivation body Gamma (eqn t t')) (h : Derivation body Gamma (eqn s t)) :
    Derivation body Gamma (eqn s' t') := trans (symm ds) (trans h dt)

def pairZeroZero (body : Positive (Fin 1)) (α : Type) : Derivation body [] (pair (z : OTerm α) z) := by
  apply Derivation.conjunctionIntroduction
  · exact Derivation.implicationIntroduction (refl z)
  · apply Derivation.conjunctionIntroduction
    · apply Derivation.implicationIntroduction
      exact zeroNeSuc (align doubleZero (congSuc doubleZero) (Derivation.hypothesis List.mem_cons_self))
    · apply Derivation.implicationIntroduction
      exact sucNeZeroApply (align (congSuc doubleZero) doubleZero (Derivation.hypothesis List.mem_cons_self))

def pairZeroSucc (body : Positive (Fin 1)) {α : Type} (t : OTerm α) :
    Derivation body [] (pair z (suc t)) := by
  apply Derivation.conjunctionIntroduction
  · apply Derivation.implicationIntroduction
    exact Derivation.explosion (zeroNeSuc (align doubleZero (doubleSucc t) (Derivation.hypothesis List.mem_cons_self)))
  · apply Derivation.conjunctionIntroduction
    · apply Derivation.implicationIntroduction
      exact zeroNeSuc (align doubleZero (congSuc (doubleSucc t)) (Derivation.hypothesis List.mem_cons_self))
    · apply Derivation.implicationIntroduction
      exact zeroNeSuc (cancelSuc (align (congSuc doubleZero) (doubleSucc t) (Derivation.hypothesis List.mem_cons_self)))

def pairSuccZero (body : Positive (Fin 1)) {α : Type} (s : OTerm α) :
    Derivation body [] (pair (suc s) z) := by
  apply Derivation.conjunctionIntroduction
  · apply Derivation.implicationIntroduction
    exact Derivation.explosion (sucNeZeroApply (align (doubleSucc s) doubleZero (Derivation.hypothesis List.mem_cons_self)))
  · apply Derivation.conjunctionIntroduction
    · apply Derivation.implicationIntroduction
      exact sucNeZeroApply (cancelSuc (align (doubleSucc s) (congSuc doubleZero) (Derivation.hypothesis List.mem_cons_self)))
    · apply Derivation.implicationIntroduction
      exact sucNeZeroApply (align (congSuc (doubleSucc s)) doubleZero (Derivation.hypothesis List.mem_cons_self))

def pairSuccSucc (body : Positive (Fin 1)) {α : Type} (s t : OTerm α) :
    Derivation body [] ((pair s t).imp (pair (suc s) (suc t))) := by
  apply Derivation.implicationIntroduction
  apply Derivation.conjunctionIntroduction
  · apply Derivation.implicationIntroduction
    have ih : Derivation body [eqn (dbl (suc s)) (dbl (suc t)), pair s t] (pair s t) :=
      Derivation.hypothesis (by simp)
    exact congSuc (Derivation.implicationElimination (Derivation.conjunctionLeft ih)
      (cancelSuc (cancelSuc (align (doubleSucc s) (doubleSucc t) (Derivation.hypothesis List.mem_cons_self)))))
  · apply Derivation.conjunctionIntroduction
    · apply Derivation.implicationIntroduction
      have ih : Derivation body [eqn (dbl (suc s)) (suc (dbl (suc t))), pair s t] (pair s t) :=
        Derivation.hypothesis (by simp)
      exact Derivation.implicationElimination (Derivation.conjunctionLeft (Derivation.conjunctionRight ih))
        (cancelSuc (cancelSuc (align (doubleSucc s) (congSuc (doubleSucc t)) (Derivation.hypothesis List.mem_cons_self))))
    · apply Derivation.implicationIntroduction
      have ih : Derivation body [eqn (suc (dbl (suc s))) (dbl (suc t)), pair s t] (pair s t) :=
        Derivation.hypothesis (by simp)
      exact Derivation.implicationElimination (Derivation.conjunctionRight (Derivation.conjunctionRight ih))
        (cancelSuc (cancelSuc (align (congSuc (doubleSucc s)) (doubleSucc t) (Derivation.hypothesis List.mem_cons_self))))

/-- Derived directly from the existing PA induction constructor. -/
def natInduction (theta : Formula (α ⊕ Fin 1))
    (base : Derivation body Gamma (instantiate theta (emb z)))
    (step : Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) :
    Derivation body Gamma (allOne theta) :=
  Derivation.implicationElimination (Derivation.arithmetic (.induction theta))
    (Derivation.conjunctionIntroduction base
      (Derivation.universalIntroduction (Derivation.implicationIntroduction step)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
