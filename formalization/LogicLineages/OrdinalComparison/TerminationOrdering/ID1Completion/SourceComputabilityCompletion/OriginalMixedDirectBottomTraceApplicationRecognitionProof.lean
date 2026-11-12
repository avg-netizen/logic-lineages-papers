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
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceApplicationRecognitionProof
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

/-- A genuine application certificate prefix has exactly the supplied path tail,
independently of any source or endpoint interpretation. -/
theorem liftedPath (cert childCert code head tail : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left code cert)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
 (hl : Nonempty (Derivation body Delta (graph1 stepLift cert childCert))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left tail childCert)) := by
 let qs : Fin 2 → Program 1 := ![InternalUnpair.left,InternalUnpair.right]
 apply queryCases qs (Fin.cons childCert Fin.elim0) _
 intro beta j ys Theta hj hq
 rw [graph1Rename]
 simp only [consTermRename,emptyRename] at hq
 have hp' := renameInto hp j Theta hj
 have hc' := renameInto hc j Theta hj
 have hl' := renameInto hl j Theta hj
 rw [graph1Rename] at hp' hl'
 rw [graph2Rename] at hc'
 have hpair := reconstructPair (childCert.relabel j) (ys 0) (ys 1) (hq 0) (hq 1)
 have hprefix := andLeft (stepDestruction (childCert.relabel j) (ys 0) (ys 1)
   (cert.relabel j) (code.relabel j) hpair hl' hp')
 have htailA := andLeft (andRight (InternalListCodecSupportProof.consDestruction
   (code.relabel j) positionTerm (ys 0) hprefix))
 have htailB := andLeft (andRight (InternalListCodecSupportProof.consDestruction
   (code.relabel j) (head.relabel j) (tail.relabel j) hc'))
 have he := valueUnique InternalListCodec.tailCode (ys 0) (tail.relabel j)
   (Fin.cons (code.relabel j) Fin.elim0) htailA htailB
 exact outputTransport InternalUnpair.left (ys 0) (tail.relabel j)
   (Fin.cons (childCert.relabel j) Fin.elim0) he (hq 0)

/-- Reconstruct recognition at the actual selected application child from the
same tail run. No claim that an arbitrary mixed front is an application. -/
theorem applicationChild (source : Program 2) (leaf : Program 4)
 (s t cert parameter code head tail childS childT childCert next out : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left code cert)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
 (hk : Nonempty (Derivation body Delta (graph1 stepLift cert childCert)))
 (hs : Nonempty (Derivation body Delta (graph4 OriginalTransparentApplicationFunctionDefinitions.sourceFunction childS s t cert parameter)))
 (ht : Nonempty (Derivation body Delta (graph4 OriginalTransparentApplicationFunctionDefinitions.targetFunction childT s t cert parameter)))
 (hcert : Nonempty (Derivation body Delta (graph4 OriginalTransparentApplicationFunctionDefinitions.childCertificate childCert s t cert parameter)))
 (hl : Nonempty (Derivation body Delta (graph4 OriginalTransparentApplicationFunctionDefinitions.childLive next s t cert parameter)))
 (hr : Nonempty (Derivation body Delta (InternalRawListRepeat.repeatGraph (transition source leaf) out tail next)))
 (hf : Nonempty (Derivation body Delta (graph1 (finish source leaf) (suc z) out))) :
 Nonempty (Derivation body Delta
  (graph1 InternalUnpair.left tail childCert ⊓
   graph4 (recognizes source leaf) (suc z) childS childT childCert parameter)) := by
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 let ys : Fin 4 → OTerm alpha := ![childS,childT,childCert,parameter]
 let selectors : Fin 4 → Program 4 := ![
   OriginalTransparentApplicationFunctionDefinitions.sourceFunction,
   OriginalTransparentApplicationFunctionDefinitions.targetFunction,
   OriginalTransparentApplicationFunctionDefinitions.childCertificate,
   OriginalTransparentApplicationFunctionDefinitions.childParameter]
 have hh : ∀ i : Fin 4, Nonempty (Derivation body Delta
   (programGraph (selectors i) (ys i) xs)) := by
  intro i
  exact Fin.cases hs (Fin.cases ht (Fin.cases hcert
    (Fin.cases (projectionValue (3 : Fin 4) xs) (fun j => Fin.elim0 j)))) i
 have hv := compositionRecover OriginalHereditaryLambda.live selectors next xs ys hl hh
 have hchildPath := liftedPath cert childCert code head tail hp hc hk
 exact andIntro hchildPath (OriginalMixedDirectBottomTraceChildInductionProof.recognizedFromRun
  source leaf childS childT childCert parameter tail next out hchildPath hv hr hf)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceApplicationRecognitionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceApplicationRecognitionProof
