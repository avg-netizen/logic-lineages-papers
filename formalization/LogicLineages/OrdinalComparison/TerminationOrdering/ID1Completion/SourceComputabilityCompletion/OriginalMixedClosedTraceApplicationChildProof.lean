module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceAcceptanceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceDescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceFrontQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceChildRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceKnownChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceInductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceChildInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceBodySelectorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaErasureDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceLambdaChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedApplicationErasureDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationChildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedDirectBottomTrace
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalMixedClosedTraceInductionDefinitions
/-- The application child supplier is discharged only at the actual smaller
path and already reconstructed child recognizer graph. -/
theorem contextIH (source : Program 2) (leaf outLeaf : Program 4)
 (code head tail childS childT childCert childParam d cutoff c : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath source leaf outLeaf code)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tail childCert)))
 (ha : Nonempty (Derivation body Delta (graph4 (recognizes source leaf) (suc z) childS childT childCert childParam))) :
 OriginalMixedClosedApplicationErasureDefinitions.ChildIH body Delta leaf outLeaf source childS childT childCert childParam d cutoff c := by
 intro beta j Theta incl erasedS erasedT newParam gamma extended hs hl hop hnp hin hes het
 have hi' := renameInto hi j Theta incl
 have hc' := renameInto hc j Theta incl
 have hp' := renameInto hp j Theta incl
 have ha' := renameInto ha j Theta incl
 simp only [OriginalMixedClosedTraceInductionSyntaxProof.belowPathRename] at hi'
 simp only [graph2Rename] at hc'
 simp only [graph1Rename] at hp'
 simp only [graph4Rename,sucRelabel,zRelabel] at ha'
 have hr := OriginalMixedClosedTraceChildInductionProof.childResult source leaf outLeaf
  (code.relabel j) (head.relabel j) (tail.relabel j)
  (childS.relabel j) (childT.relabel j) (childCert.relabel j) (childParam.relabel j)
  newParam gamma extended (d.relabel j) (cutoff.relabel j) (c.relabel j) erasedS erasedT
  hi' hc' hp' ha' hs hl hin hop hnp hes het
 exact andRight hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationChildProof
