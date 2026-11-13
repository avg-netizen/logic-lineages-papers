module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoRootProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationRootEncodingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- A root constructor built from the actual child computations is identified
with the recursive root stored in the actual source evaluator envelope. -/
theorem actualEncoding (R : Program 2) (H G : Program 1) (M W : Program 2)
 (input parameter output inner base root rows candidate label data : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) output input parameter)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing output base inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner root rows)))
 (hc : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation
   (OriginalHereditaryEvaluatorDefinitions.evaluator R)) candidate input parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing candidate label data))) :
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing root label data)) := by
 have hr := RankMemoRootProof.actualRoot R H G M W input parameter output inner base root rows hs hv ho hi
 have he := valueUnique (OriginalRootObservation.rootObservation (OriginalHereditaryEvaluatorDefinitions.evaluator R))
   candidate root (Fin.cons input (Fin.cons parameter Fin.elim0)) hc hr
 exact outputTransport InternalPairing.pairing candidate root
   (Fin.cons label (Fin.cons data Fin.elim0)) he hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationRootEncodingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationRootEncodingProof
