module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.RecursorFreeVectorDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteScalarDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteVector
open Source Source.ForwardTranslation RecursorFreeVector

/-- Semantic finiteness at the actual canonical extracted scalar interface.
Its separate identification with the printed literal-collapse condition is not
asserted by this definition or this package. Canonical extraction is proved
available independently for every original term with a ground free context. -/
def finiteSource {Γ : List Ty} {τ : Ty} (e : OriginalTerm Γ τ) : Prop :=
  ∀ v, AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy e = some v →
    ∀ s, compileScalar (v 0) = some s → SemanticFiniteScalar.finiteHeads s

namespace Code
abbrev Input := RecursorFreeVector.Code.Input
abbrev VectorInput := RecursorFreeVector.Code.VectorInput
def decideVectors (p : VectorInput) : Option Bool := do
  let a ← SemanticFiniteScalar.Code.compile p.2.2.1.1
  let b ← SemanticFiniteScalar.Code.compile p.2.2.2.1
  let answer ← BaseBooleanSource.Code.decideClosureForall (RecursorFreeVector.Code.formula p.1 p.2.1 a b)
  return positiveFlag p.2.1 p.2.2.1 p.2.2.2 && answer

/-- Literal original-term-code pipeline: canonical assignment, original vector
compiler, finite-coefficient scalar compiler, closed BASE decision. -/
def decideSource (p : Input) : Option Bool := do
  let a ← GroundPositiveQuerySplit.vectorAt (p.1,p.2.2.1)
  let b ← GroundPositiveQuerySplit.vectorAt (p.1,p.2.2.2)
  decideVectors (p.1,p.2.1,a,b)
end Code
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SemanticFiniteVector
