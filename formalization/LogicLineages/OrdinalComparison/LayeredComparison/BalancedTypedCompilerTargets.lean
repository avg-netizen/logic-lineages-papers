module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompilerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompiler.Targets
open BalancedSyntax BalancedEvaluation

/-- Literal equality with the existing Formula.encode, for ALL typed source
certificates, expressions and integer signs. No genuineness, positivity or
lower-calibration premise restricts this exact connection to the accepted
unconditional all-code compiler. -/
def ExactTypedCodeCalibration : Prop :=
  ∀ (Γ : List Nat) (C : Certificate Γ) (E F : Syntax Γ) (desired : Int),
    BalancedRawCompiler.compileCode Γ (encodeCertificate Γ C)
        (encodeSyntax Γ E) (encodeSyntax Γ F) desired =
      (typedFormula Γ C E F desired).encode

/-- Structural support containment for ALL typed inputs, independently of
genuineness and valuation. This is the ORIGINAL pair support, before any
collection or filtering. Exact free-variable equality remains separate. -/
def OriginalSupportContainment : Prop :=
  ∀ (Γ : List Nat) (C : Certificate Γ) (E F : Syntax Γ) (desired : Int),
    ∀ i ∈ (typedFormula Γ C E F desired).variables,
      i ∈ rawVariables Γ C E ++ rawVariables Γ C F

/-- Actual-source sign truth under one genuine certificate and one raw
valuation. Positivity is required ONLY on the original pair support; every
outside coordinate remains unrestricted. The accepted guard supplier's
LowerCorrect premise must be discharged by structural induction, not passed
through as a premise here. All integer desired signs remain in the domain. -/
def ActualSignSemantics : Prop :=
  ∀ (Γ : List Nat) (C : Certificate Γ) (E F : Syntax Γ)
    (desired : Int) (ν : Nat → Nat),
    genuineCertificate Γ C →
    genuineExpression Γ E → genuineExpression Γ F →
    (∀ i ∈ rawVariables Γ C E ++ rawVariables Γ C F, 0 < ν i) →
    ((typedFormula Γ C E F desired).eval ν ↔
      Int.sign ((value Γ C E ν : Int) - (value Γ C F ν : Int)) = desired)

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompiler.Targets
