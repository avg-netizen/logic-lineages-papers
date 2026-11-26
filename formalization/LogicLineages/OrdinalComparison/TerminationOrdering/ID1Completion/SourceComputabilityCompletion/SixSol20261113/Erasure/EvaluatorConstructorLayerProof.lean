module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorLayerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLayerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorErasureDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Local layer introduction after the constructor/row induction has actually
produced its three component graphs. Not a replacement for the frozen target. -/
theorem evaluatorAtComponents (R : Program 2) (H G : Program 1) (M W : Program 2)
 (input parameter a b row inner out : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (ha : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) a input parameter)))
 (hb : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) b input parameter)))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows (OriginalHereditaryEvaluatorDefinitions.evaluator R)) row input parameter)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner b row)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out a inner))) :
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) out input parameter)) := by
 let E := OriginalHereditaryEvaluatorDefinitions.evaluator R
 let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
 have hinner := binaryValue InternalPairing.pairing (OriginalRootObservation.rootObservation E)
   (OriginalHereditaryDeletionRows.rows E) inner b row xs hi hb hr
 have hlayer := binaryValue InternalPairing.pairing (OriginalRootObservation.rootObservation R)
   (pairOf (OriginalRootObservation.rootObservation E) (OriginalHereditaryDeletionRows.rows E))
   out a inner xs ho ha hinner
 have heq := Context.EvaluatorLayerProof.actual R H G M W body alpha Delta input parameter out hs
 obtain ⟨hback⟩ := andRight heq
 exact ⟨Derivation.implicationElimination hback (Classical.choice hlayer)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLayerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLayerProof
