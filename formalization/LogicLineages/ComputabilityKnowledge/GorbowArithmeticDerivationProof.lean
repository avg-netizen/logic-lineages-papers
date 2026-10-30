module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowArithmeticDerivation
public import LogicLineages.ComputabilityKnowledge.GorbowClosedEqualityProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowArithmeticDerivationProof
open GorbowSyntax GorbowPACore GorbowStandardInstances GorbowClosedEquality GorbowArithmeticDerivation
open GorbowClosedEqualityProof

private theorem subLift (σ : Fin 1 → Term 0) (w : Term 0) :
    GorbowSubstitution.substitute σ (liftClosedTerm 1 w)=w := closedTransport 1 w σ

private theorem succProof (t u : Term 0) (p : Proof (.equal t u)) : Nonempty (Proof (.equal (.succ t) (.succ u))) := by
  have h := termCongruence (.succ (.var 0)) t u p
  simpa only [instantiateTerm,GorbowSubstitution.substitute,Fin.cases_zero] using h
private theorem addLeft (t u w : Term 0) (p : Proof (.equal t u)) : Nonempty (Proof (.equal (.add t w) (.add u w))) := by
  have h := termCongruence (.add (.var 0) (liftClosedTerm 1 w)) t u p
  simpa only [instantiateTerm,GorbowSubstitution.substitute,Fin.cases_zero,subLift] using h
private theorem addRight (t u w : Term 0) (p : Proof (.equal t u)) : Nonempty (Proof (.equal (.add w t) (.add w u))) := by
  have h := termCongruence (.add (liftClosedTerm 1 w) (.var 0)) t u p
  simpa only [instantiateTerm,GorbowSubstitution.substitute,Fin.cases_zero,subLift] using h
private theorem mulLeft (t u w : Term 0) (p : Proof (.equal t u)) : Nonempty (Proof (.equal (.mul t w) (.mul u w))) := by
  have h := termCongruence (.mul (.var 0) (liftClosedTerm 1 w)) t u p
  simpa only [instantiateTerm,GorbowSubstitution.substitute,Fin.cases_zero,subLift] using h
private theorem mulRight (t u w : Term 0) (p : Proof (.equal t u)) : Nonempty (Proof (.equal (.mul w t) (.mul w u))) := by
  have h := termCongruence (.mul (liftClosedTerm 1 w) (.var 0)) t u p
  simpa only [instantiateTerm,GorbowSubstitution.substitute,Fin.cases_zero,subLift] using h

theorem numeralAddition : Comparators.GorbowArithmeticDerivation.NumeralAddition := by
  intro a b
  induction b with
  | zero => exact ⟨.arithmetic (.addZero (Term.numeral a))⟩
  | succ b ih =>
    obtain ⟨p⟩ := ih
    obtain ⟨q⟩ := succProof _ _ p
    have hs : Proof (n:=0) (.equal (.add (Term.numeral a) (.succ (Term.numeral b)))
        (.succ (.add (Term.numeral a) (Term.numeral b)))) := .arithmetic (.addSucc _ _)
    have h := transitivity _ _ _ hs q
    change Nonempty (Proof (.equal (.add (Term.numeral a) (.succ (Term.numeral b))) (.succ (Term.numeral (a+b)))))
    exact h

theorem numeralMultiplication : Comparators.GorbowArithmeticDerivation.NumeralMultiplication := by
  intro a b
  induction b with
  | zero => exact ⟨.arithmetic (.mulZero (Term.numeral a))⟩
  | succ b ih =>
    obtain ⟨p⟩ := ih
    obtain ⟨q⟩ := addLeft _ _ (Term.numeral a) p
    have hs : Proof (n:=0) (.equal (.mul (Term.numeral a) (.succ (Term.numeral b)))
        (.add (.mul (Term.numeral a) (Term.numeral b)) (Term.numeral a))) := .arithmetic (.mulSucc _ _)
    obtain ⟨h⟩ := transitivity _ _ _ hs q
    obtain ⟨ha⟩ := numeralAddition (a*b) a
    have hc := transitivity _ _ _ h ha
    simpa only [Calculation,Term.numeral,Nat.mul_succ] using hc

theorem closedEvaluation : Comparators.GorbowArithmeticDerivation.ClosedEvaluation := by
  intro t
  induction t with
  | var i => exact Fin.elim0 i
  | zero => intro h I; exact ⟨.logical (.reflexive .zero)⟩
  | succ t ih =>
    intro h I
    cases h with
    | succ ht =>
      obtain ⟨p⟩ := ih ht I
      simpa only [Calculation,Term.realize,Term.numeral] using succProof _ _ p
  | add t u ih ih' =>
    intro h I
    cases h with
    | add ht hu =>
      obtain ⟨p⟩ := ih ht I
      obtain ⟨q⟩ := ih' hu I
      obtain ⟨p'⟩ := addLeft _ _ u p
      obtain ⟨q'⟩ := addRight _ _ (Term.numeral (t.realize I Fin.elim0)) q
      obtain ⟨pq⟩ := transitivity _ _ _ p' q'
      obtain ⟨hc⟩ := numeralAddition (t.realize I Fin.elim0) (u.realize I Fin.elim0)
      exact transitivity _ _ _ pq hc
  | mul t u ih ih' =>
    intro h I
    cases h with
    | mul ht hu =>
      obtain ⟨p⟩ := ih ht I
      obtain ⟨q⟩ := ih' hu I
      obtain ⟨p'⟩ := mulLeft _ _ u p
      obtain ⟨q'⟩ := mulRight _ _ (Term.numeral (t.realize I Fin.elim0)) q
      obtain ⟨pq⟩ := transitivity _ _ _ p' q'
      obtain ⟨hc⟩ := numeralMultiplication (t.realize I Fin.elim0) (u.realize I Fin.elim0)
      exact transitivity _ _ _ pq hc
  | universalFunction t ih => intro h; cases h

theorem equalValues : Comparators.GorbowArithmeticDerivation.EqualValues := by
  intro t u ht hu I he
  obtain ⟨p⟩ := closedEvaluation t ht I
  obtain ⟨q⟩ := closedEvaluation u hu I
  rw [he] at p
  obtain ⟨qs⟩ := symmetry _ _ q
  exact transitivity _ _ _ p qs

theorem gorbowArithmeticDerivation : Comparators.GorbowArithmeticDerivation.Target :=
  ⟨numeralAddition,numeralMultiplication,closedEvaluation,equalValues⟩
end LogicLineages.ComputabilityKnowledge.GorbowArithmeticDerivationProof
