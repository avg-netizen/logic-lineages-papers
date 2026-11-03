module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariablesDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariables.Targets
open BalancedSyntax BalancedEvaluation

/-- Unchanged truth at EVERY raw valuation and exact membership equality of
syntactic variable sets for ALL typed inputs. No genuineness or positivity
premise is allowed. This includes cancellation, empty support and every
integer desired sign. Equality is of membership, not list order/multiplicity. -/
def TruthAndExactVariables : Prop :=
  ∀ (Γ : List Nat) (C : Certificate Γ) (E F : Syntax Γ) (desired : Int),
    (∀ ν : Nat → Nat,
      (sourceFormula Γ C E F desired).eval ν ↔
        (BalancedTypedCompiler.typedFormula Γ C E F desired).eval ν) ∧
    (∀ i : Nat,
      i ∈ (sourceFormula Γ C E F desired).variables ↔
        i ∈ rawVariables Γ C E ++ rawVariables Γ C F)

/-- The padded ordinary BASE formula has the actual source sign under a
genuine certificate and genuine expressions. Positivity is required ONLY on
the ORIGINAL pair support; all other raw coordinates remain unrestricted. -/
def ActualSignSemantics : Prop :=
  ∀ (Γ : List Nat) (C : Certificate Γ) (E F : Syntax Γ)
    (desired : Int) (ν : Nat → Nat),
    genuineCertificate Γ C →
    genuineExpression Γ E → genuineExpression Γ F →
    (∀ i ∈ rawVariables Γ C E ++ rawVariables Γ C F, 0 < ν i) →
    ((sourceFormula Γ C E F desired).eval ν ↔
      Int.sign ((value Γ C E ν : Int) - (value Γ C F ν : Int)) = desired)

/-- Literal code equality with the EXISTING Formula.encode for ALL typed
inputs at EVERY shape, including []. No validity, positivity, lower-comparator
or calibration premise is supplied by the caller. -/
def ExactTypedCodeCalibration : Prop :=
  ∀ (Γ : List Nat) (C : Certificate Γ) (E F : Syntax Γ) (desired : Int),
    formulaCode Γ (encodeCertificate Γ C)
        (encodeSyntax Γ E) (encodeSyntax Γ F) desired =
      (sourceFormula Γ C E F desired).encode

/-- Uniform total computability of this SPECIFIC unchanged-compiler wrapper
on EVERY raw shape, certificate code, expression code and integer desired sign.
No source-validity premise and no claim of malformed-code semantic validity. -/
def AllCodeComputation : Prop := Computable outputCode

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariables.Targets
