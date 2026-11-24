module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionScratchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountLeftTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open NumberedWindowInternalDirectTypedUnionScratchTargets (observer)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalLiteralCount (permutation)

abbrev D {α : Type} (B : Positive (Fin 1)) (Γ : List (Formula α)) (f : Formula α) : Prop :=
  Nonempty (Derivation B Γ f)

/-- Projected head is consed to the original tape and to the selected
left projection. The right projection is the very same tape in both joins. -/
def ExactOpenProjectedCountLeft : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (head oldTail leftTail right old left joinedTail joined : OTerm α),
    D B Γ (consGraph old head oldTail) →
    D B Γ (consGraph left head leftTail) →
    D B Γ (appendGraph joinedTail leftTail right) →
    D B Γ (appendGraph joined left right) →
    D B Γ (observer permutation oldTail joinedTail) →
    D B Γ (observer permutation old joined)

end LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountLeftTargets
