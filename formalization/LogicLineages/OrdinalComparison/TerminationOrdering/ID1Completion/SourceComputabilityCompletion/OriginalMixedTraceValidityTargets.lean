module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTransparentMixedDirectBottom (source leaf)
/-- Genuine target SOURCE validity from the entire restricted trace. NEW L is
fixed: arbitrary leaves would not force the direct-bottom endpoint. No initial
oldStep validity or native calibration is assumed. -/
def ActualTargetSourceValidity : Prop := ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter : OTerm alpha),
 Nonempty (Derivation body Delta
  ((graph2 (source H G M W) (numeral 1) s parameter ⊓
    graph4 (OriginalMixedDirectBottomTrace.recognizes (source H G M W) (leaf H G M W oldStep)) (numeral 1) s t cert parameter).imp
   (graph2 (source H G M W) (numeral 1) t parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityTargets
