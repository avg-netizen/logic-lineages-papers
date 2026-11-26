module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildObservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildScanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConstructorLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildDecorationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnApplicationSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ArgumentsReturnSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedConstructorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnNumberedSubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedContentProof
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

theorem atCoordinates (Q : Program 2) (input typ raw label head encodedType base extraTypes extras parameter jobs annotatedPrefix row first resultTail second returned afterBase numberedFields afterHead afterLabel payload raw0 raw1 ann typed0 typed1 mark0 mark1 : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw (Fin.cons label (Fin.cons head (Fin.cons encodedType (Fin.cons base (Fin.cons extraTypes (Fin.cons extras Fin.elim0)))))))))
    (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)))
    (hp : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix (numeral 2) z typ raw jobs)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (observationFromJob Q)) row annotatedPrefix)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode row first resultTail)))
    (htail : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode resultTail second z)))
    (hret : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)))
    (b0 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterBase extraTypes extras)))
    (b1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing numberedFields base afterBase)))
    (b2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterHead encodedType numberedFields)))
    (b3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing afterLabel head afterHead)))
    (b4 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload label afterLabel)))
    (b5 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw0 base parameter)))
    (b6 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw1 extras parameter)))
    (b7 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ann (numeral 1) z)))
    (b8 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed0 z raw0)))
    (b9 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed1 z raw1)))
    (b10 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark0 (numeral 1) typed0)))
    (b11 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark1 (numeral 1) typed1)))
    : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter)) := by
  have hraw := NumberedConstructorProof.pair raw label head encodedType base extraTypes extras afterBase numberedFields afterHead afterLabel payload hc b0 b1 b2 b3 b4
  have hl := NumberedConstructorProof.lookup raw label head encodedType base extraTypes extras parameter jobs raw0 raw1 hc b5 b6 he
  have harity := OriginalRawSyntaxTransportInternalConstructorSelectorsProof.numberedArity (.projection 0)
    raw label head encodedType base extraTypes extras (Fin.cons raw Fin.elim0) (projectionValue 0 (Fin.cons raw Fin.elim0)) hc
  have ha0 := OriginalInternalAnnotationChildValueProof.numberedValue z z typ raw payload ann hraw b7
  have ha1 := OriginalInternalAnnotationChildValueProof.numberedValue (numeral 1) z typ raw payload ann hraw b7
  have hactive0 := OriginalInternalAnnotationChildValueProof.active z z typ raw (numeral 2) ann harity ChildDecorationProof.zeroBelowTwo ha0
  have hactive1 := OriginalInternalAnnotationChildValueProof.active (numeral 1) z typ raw (numeral 2) ann harity ChildDecorationProof.oneBelowTwo ha1
  have hd0 := ChildDecorationProof.decorateValue z z typ raw raw0 mark0 ann (numeral 1) z typed0 hactive0 b7 b8 b10
  have hd1 := ChildDecorationProof.decorateValue (numeral 1) z typ raw raw1 mark1 ann (numeral 1) z typed1 hactive1 b7 b9 b11
  have hcell0 := NarrowScanCellProof.cellValue z z typ raw jobs mark0 raw0 hd0 (andLeft hl)
  have hcell1 := NarrowScanCellProof.cellValue (numeral 1) z typ raw jobs mark1 raw1 hd1 (andRight hl)
  have hv := ChildScanProof.twoCells (observationFromJob Q) z typ raw jobs annotatedPrefix row first resultTail second mark0 mark1 raw0 raw1 hp hm hr htail hcell0 hcell1 (andLeft hl) (andRight hl)
  have hfirst := ChildObservationProof.argumentsValue Q mark0 typed0 z raw0 base parameter first b10 b8 b5 (andLeft hv)
  have hsecond := ChildObservationProof.argumentsValue Q mark1 typed1 z raw1 extras parameter second b11 b9 b6 (andRight hv)
  exact SixSol20261112.Context.ReturnSubstitutionProof.numberedSubstitution Q body alpha Delta input parameter typ raw payload label afterLabel head afterHead encodedType numberedFields base afterBase extraTypes extras first second returned hi hraw b4 b3 b2 b1 b0 hfirst hsecond hret
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedContentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedContentProof
