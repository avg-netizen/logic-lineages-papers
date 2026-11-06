module
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.ScalarDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoCounterexample.ScalarTargets
open Source Source.ForwardTranslation Source.SourceClasses PolynomialGraphCompletion
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def ExactOriginalNames : Prop := ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι),
  (scalarExpr index s).variables = (scalarNames s).map index

def ExactScalarValue : Prop := ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι) (ν : Nat → Nat),
  (scalarExpr index s).value ν = s.value (fun i => ν (index i))

def ValidPolynomialExpression : Prop :=
  ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι), PolynomialScalar s → ValidExpr (scalarExpr index s)

/-- Reuses the complete actual-source classification. Includes every original
binder and subterm in the level bound and the literal successful assignment.
The same indexed valuation is used on both sides, including repeated names. -/
def ActualLevelTwoScalar : Prop :=
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
  ∀ (τ : Ty) (p : Source.AdmissibleSum.Policy) (t : OriginalTerm Γ τ), InternalLevelBound 2 t →
  ∀ index : OrdinalComponent Γ → Nat,
  ∃ (v : OrdinalVector Γ τ.level) (s : Scalar (OrdinalComponent Γ)),
    Source.AdmissibleAssignment.assignment p t = some v ∧ compileScalar (v 0) = some s ∧
      ValidExpr (scalarExpr index s) ∧
      ∀ ν : Nat → Nat, ((scalarExpr index s).value ν : Ordinal) =
        denote (fun c => (ν (index c) : Ordinal)) (v 0)

def LiteralScalarCode : Prop := ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι),
  ScalarCode.lower (scalarCode index s) = (scalarExpr index s).encode ∧
    ScalarCode.lowerSyntax (scalarSyntaxCode index s) = (scalarExpr index s).encode

def LiteralGraphPackage : Prop := ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι) (resultName : Nat),
  ScalarCode.package (scalarSyntaxCode index s) resultName = expressionPackage (scalarExpr index s) resultName

/-- All raw codes have a numeric program; semantic correctness is separately
calibrated to genuine source syntax and polynomial heads. -/
def ActualNumericPrograms : Prop := Primrec ScalarCode.lower ∧ Primrec ScalarCode.lowerSyntax ∧
  Primrec₂ ScalarCode.package

/-- One scalar's exact functional graph, retaining all original correlations.
The result symbol may itself be an original name. This is translation only,
not a word-language decision procedure or a whole level-two comparison proof. -/
def SourceScalarGraph : Prop := ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι),
  PolynomialScalar s → ∀ (resultName : Nat) (ν : Nat → Nat),
    expressionGraph (scalarExpr index s) resultName ν ↔ ν resultName = s.value (fun i => ν (index i))
end LogicLineages.OrdinalComparison.LevelTwoCounterexample.ScalarTargets
