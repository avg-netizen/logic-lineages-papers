module
public import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginMemberRouteTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

def ExactOpenOriginMemberRoute : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (left right joined dom : OTerm α),
    Nonempty (Derivation body Γ (appendGraph joined left right)) →
    Nonempty (Derivation body Γ (memberGraph joined dom)) →
    Nonempty (Derivation body Γ
      (memberGraph left dom ⊔ ((memberGraph left dom).not ⊓ memberGraph right dom)))

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginMemberRouteTargets
