module
public import LogicLineages.OrdinalComparison.ActualArithmeticCodeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.ArithmeticCode.Proof
open Arithmetic

private theorem lift_numeral (k n : Nat) : liftCode k (numeralCode n) = numeralCode n := by
  rw [liftCode]
  have hm : numeralCode n % 4 = 0 := by simp [numeralCode]
  simp only [hm, ↓reduceIte]

private theorem lift_variable (k i : Nat) :
    liftCode k (variableCode i) = variableCode (i+k) := by
  have hm : variableCode i % 4 = 1 := by simp [variableCode]
  have hd : variableCode i / 4 = i := by unfold variableCode; omega
  rw [liftCode]
  simp only [hm, hd, Nat.one_ne_zero, ↓reduceIte]

private theorem lift_add (k a b : Nat) :
    liftCode k (addCode a b) = addCode (liftCode k a) (liftCode k b) := by
  have hm : addCode a b % 4 = 2 := by simp [addCode]
  have hd : addCode a b / 4 = Nat.pair a b := by unfold addCode; omega
  rw [liftCode]
  simp [hm, hd]

private theorem lift_scale (k n a : Nat) :
    liftCode k (scaleCode n a) = scaleCode n (liftCode k a) := by
  have hm : scaleCode n a % 4 = 3 := by simp [scaleCode]
  have hd : scaleCode n a / 4 = Nat.pair n a := by unfold scaleCode; omega
  rw [liftCode]
  simp [hm, hd]

theorem exactExpressionLift : Targets.ExactExpressionLift := by
  intro k a
  induction a with
  | numeral n => exact lift_numeral k n
  | «variable» i => exact lift_variable k i
  | add a b iha ihb =>
      simpa only [exprCode, Expr.lift, Expr.rename] using
        (lift_add k (exprCode a) (exprCode b)).trans (congrArg₂ addCode iha ihb)
  | scale n a ih =>
      simpa only [exprCode, Expr.lift, Expr.rename] using
        (lift_scale k n (exprCode a)).trans (congrArg (scaleCode n) ih)

theorem exactFormulaConstructors : Targets.ExactFormulaConstructors := by
  refine ⟨?_, ?_, ?_⟩
  · intro xs
    induction xs with
    | nil => rfl
    | cons p ps ih =>
        simpa only [List.map_cons, conjunctionCode, conjunction, List.foldr_cons, formulaCode]
          using congrArg (andCode (formulaCode p)) ih
  · intro xs
    induction xs with
    | nil => rfl
    | cons p ps ih =>
        simpa only [List.map_cons, disjunctionCode, disjunction, List.foldr_cons, formulaCode]
          using congrArg (orCode (formulaCode p)) ih
  · intros; rfl

private theorem successor_exact (a b : Expr) :
    successorCode (exprCode a) (exprCode b) = formulaCode (successor a b) := by
  rfl

private theorem phi_exact (a b : Expr) :
    phiCode (exprCode a) (exprCode b) = formulaCode (phi a b) := by
  have hd := exactFormulaConstructors.2.1
    ((List.range 4).map fun i => Formula.and (.eq a (.numeral i)) (.eq b (.numeral (Phi i))))
  simp only [List.map_map, Function.comp_def, formulaCode, exprCode] at hd
  unfold phiCode phi
  simp only [formulaCode]
  rw [hd, exactExpressionLift, exactExpressionLift]
  rfl

theorem exactFixedControl : Targets.ExactFixedControl := by
  refine ⟨successor_exact, phi_exact, ?_⟩
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
      intro a b
      simp only [phiChainCode, phiChain, formulaCode]
      rw [exactExpressionLift, exactExpressionLift]
      rw [show variableCode 0 = exprCode (.variable 0) from rfl, phi_exact, ih]
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.ArithmeticCode.Proof
