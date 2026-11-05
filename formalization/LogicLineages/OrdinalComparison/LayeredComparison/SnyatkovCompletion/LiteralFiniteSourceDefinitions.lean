module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteVectorDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LiteralFiniteSource
open Source Source.ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- The actual coefficient expressions at every literal collapse occurrence.
Both children are traversed, including a coefficient child. No simplification,
extraction success, or semantic cancellation changes this occurrence list. -/
def collapseHeads {Γ : List Ty} : OrdinalExpression Γ → List (OrdinalExpression Γ)
  | .var _ | .zero | .one | .omega => []
  | .add a b | .emul a b => collapseHeads a ++ collapseHeads b
  | .collapse a b => a :: (collapseHeads a ++ collapseHeads b)

/-- The printed finite-coefficient condition, stated on the original ordinal
syntax. Each literal head is closed and has finite ordinal value. Quantifying
all valuations makes this condition independent of a chosen environment. -/
def finiteCollapseCoefficients {Γ : List Ty} (e : OrdinalExpression Γ) : Prop :=
  ∀ c ∈ collapseHeads e, ordinalExpressionVariables c = [] ∧
    ∀ ρ : OrdinalComponent Γ → Ordinal, denote ρ c < Ordinal.omega0

/-- The condition is imposed on coordinate zero of an actual canonical
assignment. Assignment existence is part of the domain, not an implication
whose premise could fail. No scalar compiler appears in this specification. -/
def finiteSource {Γ : List Ty} {τ : Ty} (e : OriginalTerm Γ τ) : Prop :=
  ∃ v : OrdinalVector Γ τ.level,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy e = some v ∧
      finiteCollapseCoefficients (v 0)

namespace Code
/-- Executable admission test on the original term code and its ground-context
length. Canonical assignment, vector extraction, and semantic coefficient
recognition all run; failure at any stage returns false. -/
def acceptsSource (p : Nat × Nat) : Bool :=
  ((GroundPositiveQuerySplit.vectorAt p).bind
    (fun v => SemanticFiniteScalar.Code.compile v.1)).isSome
end Code
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LiteralFiniteSource
