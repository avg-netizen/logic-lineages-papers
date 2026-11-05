module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LiteralFiniteSourceDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LiteralFiniteSourceTargets
open LiteralFiniteSource Source Source.ForwardTranslation RecursorFreeVector
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def ClosedCoefficientExtraction : Prop :=
  ∀ (Γ : List Ty) (e : OrdinalExpression Γ) (c : ClosedPositive),
    extractPositive e = some c →
      ordinalExpressionVariables e = [] ∧ collapseHeads e = [] ∧
        ∀ ρ : OrdinalComponent Γ → Ordinal, c.evaluate.1.repr = denote ρ e

def LiteralScalarCorrespondence : Prop :=
  ∀ (Γ : List Ty) (e : OrdinalExpression Γ) (s : Scalar (OrdinalComponent Γ)),
    compileScalar e = some s →
      (finiteCollapseCoefficients e ↔ SemanticFiniteScalar.finiteHeads s)

def CanonicalSourceCorrespondence : Prop :=
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ τ (e : OriginalTerm Γ τ),
      finiteSource e ↔ SemanticFiniteVector.finiteSource e

def ExactSourceTest : Prop :=
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ τ (e : OriginalTerm Γ τ),
      Code.acceptsSource (Γ.length, SyntaxCode.encodeTerm e) = true ↔ finiteSource e

def ActualSourceDecision : Prop :=
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ τ (a b : OriginalTerm Γ τ), finiteSource a → finiteSource b → ∀ mode,
      ∃ (av bv : OrdinalVector Γ τ.level),
        AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a = some av ∧
        AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b = some bv ∧
        ∃ answer,
          SemanticFiniteVector.Code.decideSource
            (Γ.length, mode, SyntaxCode.encodeTerm a, SyntaxCode.encodeTerm b) = some answer ∧
          ((∀ ρ : OrdinalComponent Γ → Nat, (∀ c, 0 < ρ c) →
            sourceRelation mode av bv ρ) ↔ answer = true)

def RecursorFreePasses : Prop :=
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ τ (e : OriginalTerm Γ τ), SourceClasses.recursorFree e = true →
      finiteSource e ∧ Code.acceptsSource (Γ.length, SyntaxCode.encodeTerm e) = true

def ActualNumericPrograms : Prop :=
  Computable Code.acceptsSource ∧ Computable SemanticFiniteVector.Code.decideSource

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LiteralFiniteSourceTargets
