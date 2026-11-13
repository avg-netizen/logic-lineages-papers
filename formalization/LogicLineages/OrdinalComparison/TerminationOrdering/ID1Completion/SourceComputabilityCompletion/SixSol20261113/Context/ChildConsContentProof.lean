module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildObservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildScanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConstructorLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildDecorationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnApplicationSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ArgumentsReturnSubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConsContentProof
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

theorem atCoordinates (Q : Program 2) (raw domain child0 child1 parameter jobs annotatedPrefix row first resultTail second returned children payload raw0 raw1 ann0 ann1 typed0 typed1 mark0 mark1 packed0 : OTerm alpha)
    (hcon : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw domain child0 child1)))
    (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)))
    (hp : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix (numeral 2) (numeral 1) z raw jobs)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (observationFromJob Q)) row annotatedPrefix)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode row first resultTail)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode resultTail second z)))
    (hret : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnArgumentsCons returned raw first second)))
    (hchildren : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing children child0 child1)))
    (hpayload : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain children)))
    (hraw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 7) payload)))
    (hraw0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw0 child0 parameter)))
    (hraw1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw1 child1 parameter)))
    (ha0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ann0 z domain)))
    (ha1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ann1 (numeral 1) z)))
    (ht0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed0 domain raw0)))
    (ht1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed1 z raw1)))
    (hn0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark0 z typed0)))
    (hn1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark1 (numeral 1) typed1)))
    (hpack0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed0 domain child0)))
    : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentObservations.argumentObservations Q) returned raw parameter)) := by
  have hlookup := ChildConstructorLookupProof.consLookup raw domain child0 child1 parameter jobs raw0 raw1 hcon hraw0 hraw1 he
  have harity := OriginalRawSyntaxTransportInternalConstructorSelectorsProof.consArity (.projection 0)
    raw domain child0 child1 (Fin.cons raw Fin.elim0) (projectionValue 0 _) hcon
  have ha0child := OriginalInternalAnnotationChildBinaryProof.cons0 (numeral 1) z raw payload domain children ann0 hraw hpayload ha0
  have ha1child := OriginalInternalAnnotationChildBinaryProof.cons1 z (numeral 1) z raw payload domain children ann1 hraw hpayload ha1
  have ha0active := OriginalInternalAnnotationChildValueProof.active z (numeral 1) z raw (numeral 2) ann0 harity ChildDecorationProof.zeroBelowTwo ha0child
  have ha1active := OriginalInternalAnnotationChildValueProof.active (numeral 1) (numeral 1) z raw (numeral 2) ann1 harity ChildDecorationProof.oneBelowTwo ha1child
  have hd0 := ChildDecorationProof.decorateValue z (numeral 1) z raw raw0 mark0 ann0 z domain typed0 ha0active ha0 ht0 hn0
  have hd1 := ChildDecorationProof.decorateValue (numeral 1) (numeral 1) z raw raw1 mark1 ann1 (numeral 1) z typed1 ha1active ha1 ht1 hn1
  have hc0 := NarrowScanCellProof.cellValue z (numeral 1) z raw jobs mark0 raw0 hd0 (andLeft hlookup)
  have hc1 := NarrowScanCellProof.cellValue (numeral 1) (numeral 1) z raw jobs mark1 raw1 hd1 (andRight hlookup)
  have hvalues := ChildScanProof.twoCells (observationFromJob Q) (numeral 1) z raw jobs annotatedPrefix row first resultTail second mark0 mark1 raw0 raw1 hp hm hr ht hc0 hc1 (andLeft hlookup) (andRight hlookup)
  have hfirst := ChildObservationProof.termValue Q mark0 typed0 domain raw0 child0 parameter packed0 first hn0 ht0 hraw0 hpack0 (andLeft hvalues)
  have hsecond := ChildObservationProof.argumentsValue Q mark1 typed1 z raw1 child1 parameter second hn1 ht1 hraw1 (andRight hvalues)
  exact SixSol20261112.Context.ArgumentsReturnSubstitutionProof.consSubstitution Q body alpha Delta raw domain child0 child1 packed0 first second parameter returned hcon hpack0 hfirst hsecond hret
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConsContentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConsContentProof
