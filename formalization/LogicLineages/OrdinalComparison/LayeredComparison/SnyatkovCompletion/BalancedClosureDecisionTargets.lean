module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecisionDefinitions
public import Mathlib.Computability.Partrec
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecisionSupplierTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecisionTargets
open BalancedSyntax BalancedEvaluation BalancedClosureDecision

def ExactPositiveGuard : Prop := ∀ (names : List Nat) (ν : Nat → Nat),
  (positiveFormula names).eval ν ↔ ∀ i ∈ names, 0 < ν i

def LiteralGuardCode : Prop := ∀ names : List Nat,
  positiveCode names = (positiveFormula names).encode

def ExactTypedCodeCalibration : Prop := ∀ (Γ : List Nat) (C : Certificate Γ)
    (E F : Syntax Γ) (desired : Int),
  let a : BalancedClosureDecision.Input := (Γ, encodeCertificate Γ C, encodeSyntax Γ E, encodeSyntax Γ F, desired)
  existsCode a = (existsFormula Γ C E F desired).encode ∧
    forallCode a = (forallFormula Γ C E F desired).encode

def ActualGuardedSemantics : Prop := ∀ (Γ : List Nat) (C : Certificate Γ)
    (E F : Syntax Γ) (desired : Int) (ν : Nat → Nat),
  genuineCertificate Γ C → genuineExpression Γ E → genuineExpression Γ F →
  ((existsFormula Γ C E F desired).eval ν ↔
    (∀ i ∈ rawVariables Γ C E ++ rawVariables Γ C F, 0 < ν i) ∧
      Int.sign ((value Γ C E ν : Int) - (value Γ C F ν : Int)) = desired) ∧
  ((forallFormula Γ C E F desired).eval ν ↔
    ((∀ i ∈ rawVariables Γ C E ++ rawVariables Γ C F, 0 < ν i) →
      Int.sign ((value Γ C E ν : Int) - (value Γ C F ν : Int)) = desired))

def ActualSourceClosures : Prop := ∀ (Γ : List Nat) (C : Certificate Γ)
    (E F : Syntax Γ) (desired : Int) (b : Bool),
  genuineCertificate Γ C → genuineExpression Γ E → genuineExpression Γ F →
  let a : BalancedClosureDecision.Input := (Γ, encodeCertificate Γ C, encodeSyntax Γ E, encodeSyntax Γ F, desired)
  (existsAnswer a = some b ↔
    ((∃ ν : Nat → Nat, (∀ i ∈ rawVariables Γ C E ++ rawVariables Γ C F, 0 < ν i) ∧
      Int.sign ((value Γ C E ν : Int) - (value Γ C F ν : Int)) = desired) ↔ b = true)) ∧
  (forallAnswer a = some b ↔
    ((∀ ν : Nat → Nat, (∀ i ∈ rawVariables Γ C E ++ rawVariables Γ C F, 0 < ν i) →
      Int.sign ((value Γ C E ν : Int) - (value Γ C F ν : Int)) = desired) ↔ b = true))

/-- Computability on every raw input; semantic correctness above is for the
original genuine typed certificate/expressions, not malformed raw codes. -/
def ActualAllCodePrograms : Prop := Primrec positiveCode ∧
  Computable existsCode ∧ Computable forallCode ∧ Computable existsAnswer ∧ Computable forallAnswer

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecisionTargets
