module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedDirectBottomDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual direct-bottom branch introduction into the NEW standalone mixed leaf. No old-final identity, global package, or erasure conclusion. -/
def ActualIntroduction : Prop := ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4) (window : Program 1)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (s t cert parameter typ : OTerm alpha),
 Nonempty (Derivation body Delta
  ((OriginalTransparentDirectBottom.Premises (OriginalTransparentMixedDirectBottom.source H G M W) s t cert parameter typ).imp
   (graph4 (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window) InternalOriginalStepGuard.one s t cert parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomTargets
