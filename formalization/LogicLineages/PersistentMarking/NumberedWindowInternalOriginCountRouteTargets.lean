module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginMemberRouteTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionScratchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginCountRouteTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalDirectTypedUnionScratchTargets (observer)
open NumberedWindowInternalLiteralCount (permutation)

def ExactOpenChosenOriginCountRoute : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (removed left right joined dom : OTerm α),
    Nonempty (Derivation body Γ (observer permutation removed joined)) →
    Nonempty (Derivation body Γ (appendGraph joined left right)) →
    Nonempty (Derivation body Γ (memberGraph removed dom)) →
    Nonempty (Derivation body Γ
      (memberGraph left dom ⊔ ((memberGraph left dom).not ⊓ memberGraph right dom)))

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginCountRouteTargets
