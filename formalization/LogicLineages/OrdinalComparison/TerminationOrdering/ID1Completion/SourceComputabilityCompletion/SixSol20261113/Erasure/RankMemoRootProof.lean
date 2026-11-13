module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorLayerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsBoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoRootProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualRoot (R : Program 2) (H G : Program 1) (M W : Program 2)
 (input parameter output inner baseRoot recursiveRoot row : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) output input parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing output baseRoot inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner recursiveRoot row))) :
 Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation
   (OriginalHereditaryEvaluatorDefinitions.evaluator R)) recursiveRoot input parameter)) := by
 obtain ⟨he⟩ := Context.EvaluatorLayerProof.actual R H G M W body alpha Delta input parameter output hs
 obtain ⟨hv⟩ := hv
 have hlayer := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionLeft he) hv)
 have hall := OriginalHereditaryObservationLayerInternalProof.recovery R
   (OriginalHereditaryEvaluatorDefinitions.evaluator R) input parameter output inner baseRoot recursiveRoot row ho hi hlayer
 exact andLeft (andRight hall)


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoRootProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoRootProof
