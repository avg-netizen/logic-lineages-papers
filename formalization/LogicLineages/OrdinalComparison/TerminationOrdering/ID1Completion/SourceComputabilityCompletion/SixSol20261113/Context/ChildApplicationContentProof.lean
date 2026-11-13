module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildObservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildScanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConstructorLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildDecorationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnApplicationSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ArgumentsReturnSubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildApplicationContentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeel (graph5)
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ChildContentDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph OriginalHereditaryAnnotatedExpansion.annotation
  OriginalHereditaryAnnotatedExpansion.decorate OriginalHereditaryAnnotatedExpansion.scan

theorem atCoordinates (Q : Program 2) (input typ raw domain child0 child1 fnType parameter jobs annotatedPrefix row first resultTail second returned children payload raw0 raw1 ann0 ann1 typed0 typed1 mark0 mark1 packed0 packed1 : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
    (hcon : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor raw domain child0 child1)))
    (hfnType : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode fnType domain typ)))
    (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)))
    (hp : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix (numeral 2) z typ raw jobs)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (observationFromJob Q)) row annotatedPrefix)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode row first resultTail)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode resultTail second z)))
    (hret : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)))
    (hchildren : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing children child0 child1)))
    (hpayload : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain children)))
    (hraw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 2) payload)))
    (hraw0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw0 child0 parameter)))
    (hraw1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw1 child1 parameter)))
    (ha0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ann0 z fnType)))
    (ha1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ann1 z domain)))
    (ht0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed0 fnType raw0)))
    (ht1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed1 domain raw1)))
    (hn0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark0 z typed0)))
    (hn1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark1 z typed1)))
    (hpack0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed0 fnType child0)))
    (hpack1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed1 domain child1)))
    : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter)) := by
  have hlookup := ChildConstructorLookupProof.applicationLookup raw domain child0 child1 parameter jobs raw0 raw1 hcon hraw0 hraw1 he
  have harity := OriginalRawSyntaxTransportInternalConstructorSelectorsProof.applicationArity (.projection 0)
    raw domain child0 child1 (Fin.cons raw Fin.elim0) (projectionValue 0 (Fin.cons raw Fin.elim0)) hcon
  have ha0child := OriginalInternalAnnotationChildBinaryProof.application0 z typ raw payload domain children fnType ann0 hraw hpayload hfnType ha0
  have ha1child := OriginalInternalAnnotationChildBinaryProof.application1 z z typ raw payload domain children ann1 hraw hpayload ha1
  have ha0active := OriginalInternalAnnotationChildValueProof.active z z typ raw (numeral 2) ann0 harity ChildDecorationProof.zeroBelowTwo ha0child
  have ha1active := OriginalInternalAnnotationChildValueProof.active (numeral 1) z typ raw (numeral 2) ann1 harity ChildDecorationProof.oneBelowTwo ha1child
  have hd0 := ChildDecorationProof.decorateValue z z typ raw raw0 mark0 ann0 z fnType typed0 ha0active ha0 ht0 hn0
  have hd1 := ChildDecorationProof.decorateValue (numeral 1) z typ raw raw1 mark1 ann1 z domain typed1 ha1active ha1 ht1 hn1
  have hc0 := NarrowScanCellProof.cellValue z z typ raw jobs mark0 raw0 hd0 (andLeft hlookup)
  have hc1 := NarrowScanCellProof.cellValue (numeral 1) z typ raw jobs mark1 raw1 hd1 (andRight hlookup)
  have hvalues := ChildScanProof.twoCells (observationFromJob Q) z typ raw jobs annotatedPrefix row first resultTail second mark0 mark1 raw0 raw1 hp hm hr ht hc0 hc1 (andLeft hlookup) (andRight hlookup)
  have hfirst := ChildObservationProof.termValue Q mark0 typed0 fnType raw0 child0 parameter packed0 first hn0 ht0 hraw0 hpack0 (andLeft hvalues)
  have hsecond := ChildObservationProof.termValue Q mark1 typed1 domain raw1 child1 parameter packed1 second hn1 ht1 hraw1 hpack1 (andRight hvalues)
  exact SixSol20261112.Context.ReturnSubstitutionProof.applicationSubstitution Q body alpha Delta input parameter typ raw payload domain children child0 child1 fnType packed0 packed1 first second returned hi hraw hpayload hchildren hfnType hpack0 hpack1 hfirst hsecond hret
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildApplicationContentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildApplicationContentProof
