module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherLeafTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyActiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionAcceptedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherDomainProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- The structural preminimum domain contains actual window and original source,
not an opaque calibration hypothesis. -/
theorem domainFields (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (input parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W input parameter))) :
 Nonempty (Derivation body Delta
   (OriginalFunctionNeutrality.windowGraph p.window input parameter ⊓
    graph2 (OriginalStructuralClassKeyDefinitions.prior p H G W).base.oldSource (numeral 1) input parameter)) := by
 let q := OriginalStructuralClassKeyDefinitions.inputs p H G W
 have ha := andRight hd
 exact conjunctionRecover (BottomRepresentative.windowAt q.window)
   (OriginalTransparentDecoderSelection.transparentInputs H G W q).base.oldSource
   (Fin.cons input (Fin.cons parameter Fin.elim0)) ha

theorem corePremises (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (input output typ parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W input parameter)))
 (hk : Nonempty (Derivation body Delta (graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) output input parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input))) :
 Nonempty (Derivation body Delta (OriginalLambdaTraversalOutput.premises
   (OriginalStructuralClassKeyDefinitions.prior p H G W).base p.window output input typ parameter)) := by
 have hf := domainFields p H G W input parameter hd
 have hv := OriginalStructuralKeyActivationProof.oldLeafSource p H G W input parameter (andRight hf)
 have ha : Nonempty (Derivation body Delta (OriginalStructuralClassKeyDefinitions.Active p H G W input parameter)) := by
   change Nonempty (Derivation body Delta (graph2 (OriginalFunctionNeutrality.active
     (OriginalLambdaTraversalSelection.transparentData (OriginalStructuralClassKeyDefinitions.prior p H G W).base) p.window)
     InternalOriginalStepGuard.one input parameter))
   rw [OriginalLambdaTraversalFinalGuardProof.activeLeaf]
   exact conjunctionAccept _ _ (Fin.cons input (Fin.cons parameter Fin.elim0)) (andLeft hf) hv
 have hc := OriginalStructuralClassKeyActiveProof.keyToCore p H G W input output parameter ha hk
 exact andIntro (andLeft hf) (andIntro (andIntro hv ht) hc)

theorem keyObservations (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (input output parameter mark : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W input parameter)))
 (hk : Nonempty (Derivation body Delta (graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) output input parameter))) :
 Nonempty (Derivation body Delta (OriginalLambdaTraversalObserver.observations output input mark)) := by
 apply programCases InternalUnpair.left (Fin.cons input Fin.elim0) _
 intro beta j Theta typ hj ht
 have hd' := renameInto hd j Theta hj
 have hk' := renameInto hk j Theta hj
 rw [OriginalActiveKernelMinimumSupportProof.domainRename] at hd'
 rw [graph2Rename] at hk'
 simp only [consTermRename,emptyRename] at ht
 rw [OriginalLambdaTraversalObserverSyntaxProof.observationsRename]
 exact OriginalLambdaTraversalObserverProof.observationsAtInput
   (OriginalStructuralClassKeyDefinitions.prior p H G W).base p.window
   (output.relabel j) (input.relabel j) typ (parameter.relabel j) (mark.relabel j)
   (corePremises p H G W _ _ _ _ hd' hk' ht)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherDomainProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherDomainProof
