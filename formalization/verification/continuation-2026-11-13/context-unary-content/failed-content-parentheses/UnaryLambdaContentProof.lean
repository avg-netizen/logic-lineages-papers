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
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryLambdaContentProof
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

theorem atCoordinates (Q : Program 2) (input typ raw domain child codomain parameter jobs annotatedPrefix row first second returned payload rawCell ann typed mark packed context gamma extended childParameter : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw))))
    (hcon : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw domain child))))
    (htype : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode typ domain codomain))))
    (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter))))
    (hp : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix (numeral 1) z typ raw jobs))))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (observationFromJob Q)) row annotatedPrefix))))
    (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode row first z))))
    (hret : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second))))
    (hpayload : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain child))))
    (hrawCell : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawCell child childParameter))))
    (ha : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ann z codomain))))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed codomain rawCell))))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark z typed))))
    (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed codomain child))))
    (hparameter : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma))))
    (hextended : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended domain gamma))))
    (hchildParameter : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter context extended))))
    : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter))) := by
  have hraw := UnaryConstructorProof.lambdaPair raw domain child payload hcon hpayload
  have hpar := UnaryParameterProof.parameterValue raw domain child parameter context gamma extended childParameter hcon hparameter hextended hchildParameter
  have hl := UnaryConstructorProof.lambdaLookup raw domain child parameter childParameter jobs rawCell hcon hrawCell hpar he
  have harity := OriginalRawSyntaxTransportInternalConstructorSelectorsProof.lambdaArity (.projection 0) raw domain child (Fin.cons raw Fin.elim0) (projectionValue 0 (Fin.cons raw Fin.elim0)) hcon
  have hchild := OriginalInternalAnnotationChildValueProof.lambdaValue z z typ raw payload domain codomain ann hraw htype ha
  have hactive := OriginalInternalAnnotationChildValueProof.active z z typ raw (numeral 1) ann harity UnaryConstructorProof.zeroBelowOne hchild
  have hd := ChildDecorationProof.decorateValue z z typ raw rawCell mark ann z codomain typed hactive ha ht hn
  have hc := NarrowScanCellProof.cellValue z z typ raw jobs mark rawCell hd hl
  have hv := UnaryScanProof.oneCell (observationFromJob Q) z typ raw jobs annotatedPrefix row first mark rawCell hp hm hr hc hl
  have hfirst := ChildObservationProof.termValue Q mark typed codomain rawCell child childParameter packed first hn ht hrawCell hpacked hv
  exact SixSol20261112.Context.ReturnSubstitutionProof.lambdaSubstitution Q body alpha Delta input parameter typ raw payload domain child codomain packed context gamma extended childParameter first second returned hi hraw hpayload htype hpacked hparameter hextended hchildParameter hfirst hret
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryLambdaContentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryLambdaContentProof
