module

public import LogicLineages.ComputabilityKnowledge.GorbowPRNegativeNumeralsTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculationProof
public import LogicLineages.ComputabilityKnowledge.GorbowClassicalDerivationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRNegativeNumerals.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations
open GorbowPRNumeralCalculation GorbowTheoryProof GorbowClosedEquality GorbowStandardInstances

private theorem symmetryImplication (A : Sentence → Prop) (t u : Term 0) :
    Nonempty (Derivation A (.imp (.equal t u) (.equal u t))) := by
  let B := GorbowClosedDeduction.extend A (.equal t u)
  have hp : Derivation B (.equal t u) := by
    simpa only [GorbowClosedDeductionProof.closedSyntax.1] using
      (Derivation.axiom (A:=B) (n:=0) (.equal t u) (Or.inr rfl))
  obtain ⟨hq⟩ := GorbowTheoryEqualityProof.symmetry B t u hp
  have h := GorbowClosedDeductionProof.deduction A (.equal t u) 0 (.equal u t) hq
  simpa only [GorbowClosedDeductionProof.closedSyntax.1] using h

theorem unequalNumerals : Targets.UnequalNumerals := by
  intro A a
  induction a with
  | zero =>
      intro b hne
      cases b with
      | zero => exact False.elim (hne rfl)
      | succ b =>
          obtain ⟨hi⟩ := symmetryImplication A .zero (.succ (Term.numeral b))
          have hn : Derivation (n:=0) A (.neg (.equal (.succ (Term.numeral b)) .zero)) :=
            .arithmetic (.succNotZero (Term.numeral b))
          exact GorbowClassicalDerivation.Proof.modusTollens A _ _ hi hn
  | succ a ih =>
      intro b hne
      cases b with
      | zero => exact ⟨.arithmetic (.succNotZero (Term.numeral a))⟩
      | succ b =>
          have hab : a ≠ b := fun h => hne (congrArg Nat.succ h)
          obtain ⟨hn⟩ := ih b hab
          have hi : Derivation (n:=0) A (.imp
              (.equal (.succ (Term.numeral a)) (.succ (Term.numeral b)))
              (.equal (Term.numeral a) (Term.numeral b))) :=
            .arithmetic (.succInjective (Term.numeral a) (Term.numeral b))
          exact GorbowClassicalDerivation.Proof.modusTollens A _ _ hi hn

private theorem negativeInstance (t u : Term 0) :
    instantiate (.neg (.equal (.var 0) (liftClosedTerm 1 u))) t = .neg (.equal t u) := by
  change Formula.neg (instantiate (.equal (.var 0) (liftClosedTerm 1 u)) t) = _
  rw [GorbowClosedEqualityProof.instantiatedEqual,
    GorbowClosedEqualityProof.instantiateVariable, GorbowClosedEqualityProof.instantiateLift]

theorem negativeCalculation : Targets.NegativeCalculation := by
  intro n p tag m q ht v value hne
  obtain ⟨hp⟩ := GorbowPRNumeralCalculation.Proof.numeralCalculation n p tag m q ht v
  obtain ⟨hs⟩ := GorbowTheoryEqualityProof.symmetry (Theory p) _ _ hp
  obtain ⟨hn⟩ := unequalNumerals (Theory p) (evaluate q v) value hne
  let phi : Formula 1 := .neg (.equal (.var 0) (liftClosedTerm 1 (Term.numeral value)))
  obtain ⟨hi⟩ := GorbowTheoryEqualityProof.formulaImplication (Theory p) phi
    (Term.numeral (evaluate q v)) (call tag (numeralArguments v)) hs
  have hn' : Derivation (Theory p) (instantiate phi (Term.numeral (evaluate q v))) := by
    simpa only [phi, negativeInstance] using hn
  exact ⟨by simpa only [phi, negativeInstance] using Derivation.mp hi hn'⟩

theorem negativeExactness : Targets.NegativeExactness := by
  intro n p tag m q ht v value
  constructor
  · rintro ⟨proof⟩
    let I : Interpretation := ⟨fun _ => False, fun _ => 0, fun _ => False,
      fun _ => False, fun _ _ => False, fun _ => False⟩
    have h := GorbowPRDefiningEquations.Proof.theorySoundness n p _ proof I
    change ¬ ((call tag (numeralArguments v)).realize (interpretation p I) Fin.elim0 =
      (Term.numeral value).realize (interpretation p I) Fin.elim0) at h
    rw [GorbowPRDefiningEquations.Proof.termCalibration 0 n p tag m q
      (numeralArguments v) I Fin.elim0 ht, numeral_realize] at h
    have hv : (numeralArguments v).map (fun t => t.realize (interpretation p I) Fin.elim0) = v := by
      apply List.Vector.ext
      intro i
      simp [numeralArguments, numeral_realize]
    simpa only [hv] using h
  · exact negativeCalculation n p tag m q ht v value

end LogicLineages.ComputabilityKnowledge.GorbowPRNegativeNumerals.Proof
