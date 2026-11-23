module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginCountRouteTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginBothRemovedNonemptyTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalDirectTypedUnionScratchTargets (observer)
open NumberedWindowInternalLiteralCount (permutation)

abbrev D {α : Type} (B : Positive (Fin 1)) (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)

def ExactOpenOriginBothRemovedNotNil : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (removed head tail left right joined : OTerm α),
    D B Γ (consGraph removed head tail) →
    D B Γ (appendGraph joined left right) →
    D B Γ (observer permutation removed joined) →
    D B Γ ((eqn left z ⊓ eqn right z).not)

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginBothRemovedNonemptyTargets
