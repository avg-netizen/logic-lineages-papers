module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildObservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildScanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConstructorLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildDecorationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnApplicationSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ArgumentsReturnSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryScanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryParameterProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnLambdaSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnOrdinarySubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryOrdinaryContentProof
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

theorem atCoordinates (Q : Program 2) (input typ raw domain child parameter jobs annotatedPrefix row first second returned payload rawCell ann typed mark : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw))))
    (hcon : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw domain child))))
    (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter))))
    (hp : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix (numeral 1) z typ raw jobs))))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (observationFromJob Q)) row annotatedPrefix))))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode row first z))))
    (hret : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second))))
    (hpayload : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain child))))
    (hrawCell : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawCell child parameter))))
    (ha : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ann (numeral 1) z))))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed z rawCell))))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark (numeral 1) typed))))
    : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter))) := by
  have hraw := UnaryConstructorProof.ordinaryPair raw domain child payload hcon hpayload
  have hl := UnaryConstructorProof.ordinaryLookup raw domain child parameter jobs rawCell hcon hrawCell he
  have harity := OriginalRawSyntaxTransportInternalConstructorSelectorsProof.ordinaryArity (.projection 0) raw domain child (Fin.cons raw Fin.elim0) (projectionValue 0 (Fin.cons raw Fin.elim0)) hcon
  have hchild := OriginalInternalAnnotationChildValueProof.ordinaryValue z z typ raw payload ann hraw ha
  have hactive := OriginalInternalAnnotationChildValueProof.active z z typ raw (numeral 1) ann harity UnaryConstructorProof.zeroBelowOne hchild
  have hd := ChildDecorationProof.decorateValue z z typ raw rawCell mark ann (numeral 1) z typed hactive ha ht hn
  have hc := NarrowScanCellProof.cellValue z z typ raw jobs mark rawCell hd hl
  have hv := UnaryScanProof.oneCell (observationFromJob Q) z typ raw jobs annotatedPrefix row first mark rawCell hp hm hr hc hl
  have hfirst := ChildObservationProof.argumentsValue Q mark typed z rawCell child parameter first hn ht hrawCell hv
  exact SixSol20261112.Context.ReturnSubstitutionProof.ordinarySubstitution Q body alpha Delta input parameter typ raw payload domain child first second returned hi hraw hpayload hfirst hret
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryOrdinaryContentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryOrdinaryContentProof
