module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceAcceptanceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceDescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceFrontQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceChildRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceChildInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceLambdaChildProof
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

/-- Actual lambda-selector child reconstruction from a selected branch's tail run.
This does not assert that every mixed recognized front is a lambda. -/
theorem lambdaChild (source : Program 2) (leaf : Program 4)
 (s t cert parameter code head tail childS childT childCert childParam next out : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left code cert)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
 (hs : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.sourceBody childS s t cert parameter)))
 (ht : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.targetBody childT s t cert parameter)))
 (hk : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.childCertificate childCert s t cert parameter)))
 (hm : Nonempty (Derivation body Delta (graph4 OriginalLambdaGuardLeaf.childParameter childParam s t cert parameter)))
 (hl : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.childLive next s t cert parameter)))
 (hr : Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph (transition source leaf) out tail next)))
 (hf : Nonempty (Derivation body Delta (graph1 (finish source leaf) (suc z) out))) :
 Nonempty (Derivation body Delta
  (graph1 InternalUnpair.left tail childCert ⊓
   graph4 (recognizes source leaf) (suc z) childS childT childCert childParam)) := by
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 let ys : Fin 4 → OTerm alpha := ![childS,childT,childCert,childParam]
 have hh : ∀ i : Fin 4, Nonempty (Derivation body Delta
   (programGraph ((![OriginalLambdaGuardLeaf.sourceBody,OriginalLambdaGuardLeaf.targetBody,
     OriginalLambdaGuardLeaf.childCertificate,OriginalLambdaGuardLeaf.childParameter] : Fin 4 → Program 4) i) (ys i) xs)) := by
  intro i
  exact Fin.cases hs (Fin.cases ht (Fin.cases hk (Fin.cases hm (fun j => Fin.elim0 j)))) i
 have hv := compositionRecover OriginalHereditaryLambda.live
  (![OriginalLambdaGuardLeaf.sourceBody,OriginalLambdaGuardLeaf.targetBody,
    OriginalLambdaGuardLeaf.childCertificate,OriginalLambdaGuardLeaf.childParameter] : Fin 4 → Program 4)
  next xs ys hl hh
 have hpath := unaryValue InternalUnpair.left (.projection 2) code cert xs hp
   (projectionValue (2 : Fin 4) xs)
 have htail := andLeft (andRight (InternalListCodecSupportProof.consDestruction code head tail hc))
 have hchildPath := OriginalHereditaryLambdaChildRunProof.strippedPath xs childCert code tail hpath htail hk
 exact andIntro hchildPath (OriginalMixedDirectBottomTraceChildInductionProof.recognizedFromRun
  source leaf childS childT childCert childParam tail next out hchildPath hv hr hf)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceLambdaChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceLambdaChildProof
