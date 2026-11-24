module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginFilterConsCasesTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountLeftTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountNilTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalOriginFilterConsCasesTargets (filterGraph)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (scratchTargets)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary z)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalDirectTypedUnionScratchTargets (observer)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalProjectedCountLeftTargets (D)

def ExactOpenProjectedCountNil : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (pool outL outR projected projectedL projectedR joined : OTerm α),
    D B Γ (filterGraph true outL z pool) →
    D B Γ (filterGraph false outR z pool) →
    D B Γ (unary scratchTargets (suc projected) z) →
    D B Γ (unary scratchTargets (suc projectedL) outL) →
    D B Γ (unary scratchTargets (suc projectedR) outR) →
    D B Γ (appendGraph joined projectedL projectedR) →
    D B Γ (observer permutation projected joined)

end LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountNilTargets
