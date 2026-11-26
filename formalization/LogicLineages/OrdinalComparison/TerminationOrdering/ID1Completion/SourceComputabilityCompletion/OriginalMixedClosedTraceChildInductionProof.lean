module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceInductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceDescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceChildInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedDirectBottomTrace OriginalMixedClosedTraceInductionDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Shared by lambda and application: actual tail path, child state and tail run reconstruct recognition at exactly that child tuple. -/
theorem recognizedFromRun (source : Program 2) (leaf : Program 4)
 (childS childT childCert childParam tail next out : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tail childCert)))
 (hl : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live next childS childT childCert childParam)))
 (hr : Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph (transition source leaf) out tail next)))
 (hf : Nonempty (Derivation body Delta (graph1 (finish source leaf) (suc z) out))) :
 Nonempty (Derivation body Delta (graph4 (recognizes source leaf) (suc z) childS childT childCert childParam)) := by
 let ys : Fin 4 → OTerm alpha := ![childS,childT,childCert,childParam]
 have hpath := unaryValue InternalUnpair.left (.projection 2) tail childCert ys hp (projectionValue 2 ys)
 have hrun := binaryValue (InternalRawListRepeat.repeatProgram (transition source leaf))
  OriginalHereditaryLambda.path OriginalHereditaryLambda.live out tail next ys hr hpath hl
 exact unaryValue (finish source leaf) (run source leaf) (suc z) out ys hf hrun

/-- Actual smaller original path discharges the complete internal child row.
Recognition/source/leaf inputs are explicit here and must be supplied by actual dispatch; this helper is not the final theorem. -/
theorem childResult (source : Program 2) (leaf outLeaf : Program 4)
 (code head tail childS childT childCert childParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath source leaf outLeaf code)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tail childCert)))
 (ha : Nonempty (Derivation body Delta (graph4 (recognizes source leaf) (suc z) childS childT childCert childParam)))
 (hs : Nonempty (Derivation body Delta (graph2 source (suc z) childS childParam)))
 (hl : Nonempty (Derivation body Delta (graph4 leaf (suc z) childS childT childCert childParam)))
 (hext : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert d cutoff gamma extended)))
 (hop : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParam c extended)))
 (hnp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParam c gamma)))
 (hes : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff childS)))
 (het : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff childT))) :
 Nonempty (Derivation body Delta (result source outLeaf childS childT newParam erasedS erasedT)) := by
 have hless := InternalListCodecDecompositionSupportProof.consTailDescent code head tail hc
 have hfields := andIntro hp (andIntro hs (andIntro hl (andIntro ha (andIntro hext (andIntro hop (andIntro hnp (andIntro hes het)))))))
 exact OriginalMixedClosedTraceInductionBindingProof.belowPathApply source leaf outLeaf code tail
  childS childT childCert childParam newParam gamma extended d cutoff c erasedS erasedT hi hless hfields
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceChildInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceChildInductionProof
