module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorLayerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsBoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureRowProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Recover the literal hereditary row from an actual evaluator result using
only original source admission and the proved internal layer equation. -/
theorem rowAt (R : Program 2) (H G : Program 1) (M W : Program 2)
 (input parameter output inner baseRoot recursiveRoot row : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) output input parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing output baseRoot inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner recursiveRoot row))) :
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows
   (OriginalHereditaryEvaluatorDefinitions.evaluator R)) row input parameter)) := by
 obtain ⟨he⟩ := Context.EvaluatorLayerProof.actual R H G M W body alpha Delta input parameter output hs
 obtain ⟨hv⟩ := hv
 have hlayer := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionLeft he) hv)
 have hall := OriginalHereditaryObservationLayerInternalProof.recovery R
   (OriginalHereditaryEvaluatorDefinitions.evaluator R) input parameter output inner baseRoot recursiveRoot row ho hi hlayer
 exact andRight (andRight hall)

theorem cellAt (Q : Program 2) (input parameter c gamma count cutoff row value : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count gamma)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) row input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value cutoff row))) :
 Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation Q) value cutoff input parameter)) := by
 obtain ⟨hi⟩ := OriginalHereditaryDeletionRowsBoundProof.indexedRows Q body alpha Delta
   input parameter gamma count row cutoff value
 obtain ⟨hfields⟩ := andIntro (pairRight parameter c gamma hp)
   (andIntro hl (andIntro hb (andIntro hr hv)))
 exact ⟨Derivation.implicationElimination hi hfields⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureRowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureRowProof
