module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanBranchesTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginCountRouteTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept rowAccept)
open NumberedWindowInternalDirectInsertedRowCasesTargets (Reports)
open NumberedWindowInternalOriginRowsFilterTargets (rowStep)
open NumberedWindowInternalOpenOriginScanIntroTargets (D)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalDirectTypedUnionScratchTargets (observer)
open NumberedWindowInternalLiteralCount (permutation)

def ExactOpenOriginScanRoutedHead : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (removed decoded row rawLeft rawRight scratchLeft scratchRight
      joined tailLeft tailRight outLeft outRight : OrdinaryArithmetic.Term α),
    D B Γ (rowAccept r row removed) →
    D B Γ (unary parser (suc decoded) removed) →
    D B Γ (unary parser (suc scratchLeft) rawLeft) →
    D B Γ (unary parser (suc scratchRight) rawRight) →
    D B Γ (observer permutation decoded joined) →
    D B Γ (appendGraph joined scratchLeft scratchRight) →
    D B Γ (loopAccept r tailLeft rawLeft) → D B Γ (loopAccept r tailRight rawRight) →
    D B Γ (programGraph (rowStep true) outLeft ![row,tailLeft,scratchLeft]) →
    D B Γ (programGraph (rowStep false) outRight ![row,tailRight,scratchLeft]) →
    D B Γ (loopAccept r outLeft rawLeft ⊓ loopAccept r outRight rawRight)

end LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadTargets
