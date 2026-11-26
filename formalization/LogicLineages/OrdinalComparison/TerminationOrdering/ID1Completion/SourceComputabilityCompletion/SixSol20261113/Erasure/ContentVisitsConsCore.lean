module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsConsCore
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z)
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Runtime ContentVisitsDefinitions ContentVisitsSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Actual prefix composition preserves the fixed reverse-map row. The head
value and tail row are literal framed outputs, not length-only witnesses. -/
theorem atValues (R : Program 2)
 (job frame tagged tailTagged headCount value tailCount tailProduced
  singleFrame singleValue combined forward tailForward produced : OTerm alpha)
 (hh : Nonempty (Derivation body Delta
   (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job headCount value)))
 (ht : Nonempty (Derivation body Delta
   (PrefixFrameDefinitions.PrefixFrame R tailTagged tailCount tailProduced)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame z job)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tagged frame tailTagged)))
 (hsf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleFrame frame z)))
 (hsv : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleValue value z)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append combined tailProduced singleValue)))
 (hforward : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode forward value tailForward)))
 (hrt : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse tailProduced tailForward)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse produced forward))) :
 Nonempty (Derivation body Delta (Counted R tagged produced)) := by
 have hreverse := OriginalReverseConsProof.actualCons body alpha Delta
   forward value tailForward singleValue tailProduced combined hforward hsv hrt ha
 have he := valueUnique OriginalTypedArgumentObservations.reverse combined produced
   (Fin.cons forward Fin.elim0) hreverse hr
 have happend := outputTransport InternalApplicationValidityStackAppend.append combined produced
   (Fin.cons tailProduced (Fin.cons singleValue Fin.elim0)) he ha
 have htags := InternalApplicationValidityStackAppendListProof.consBackward
   singleFrame frame z tailTagged tailTagged tagged hsf
   (InternalApplicationValidityStackAppendListProof.appendZeroValue tailTagged) hc
 have hsingle := PrefixFrameSingletonProof.actualSingleton R body alpha Delta
   job headCount value frame singleFrame singleValue hh hf hsf hsv
 have hprefix := PrefixFrameCompositionProof.actualConcatenation R body alpha Delta
   singleFrame tailTagged headCount tailCount singleValue tailProduced tagged produced
   hsingle ht htags happend
 exact countedIntro R tagged produced (add headCount tailCount) hprefix
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsConsCore
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsConsCore
