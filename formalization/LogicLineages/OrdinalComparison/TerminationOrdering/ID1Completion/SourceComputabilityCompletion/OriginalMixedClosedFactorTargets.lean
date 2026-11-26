module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedFactorTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Literal acceptance-factor elimination at identical four inputs. This
makes no assertion about recognizer implication or final-tuple identity. -/
def ActualRawFactor : Prop := ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4) (window : Program 1)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter : OTerm alpha),
 Nonempty (Derivation body Delta (graph4 (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window)
  InternalOriginalStepGuard.one s t cert parameter)) →
 Nonempty (Derivation body Delta (graph4 (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
  InternalOriginalStepGuard.one s t cert parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedFactorTargets
