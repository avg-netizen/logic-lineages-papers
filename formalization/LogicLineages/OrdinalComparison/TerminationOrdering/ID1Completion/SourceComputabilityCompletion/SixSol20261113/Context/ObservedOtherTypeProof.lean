module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherDomainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyActiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionAcceptedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherTypeProof
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
theorem keyType (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (input output typ parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W input parameter)))
 (hk : Nonempty (Derivation body Delta (graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) output input parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ output)) :=
 andLeft (andRight (OriginalLambdaTraversalOutputProof.invariantAtInput
   (OriginalStructuralClassKeyDefinitions.prior p H G W).base p.window output input typ parameter
   (ObservedOtherDomainProof.corePremises p H G W input output typ parameter hd hk ht)))

theorem sharedType (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (input output common typ otherType parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W input parameter)))
 (ho : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W output parameter)))
 (hk : Nonempty (Derivation body Delta (graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) common input parameter)))
 (hk' : Nonempty (Derivation body Delta (graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) common output parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input)))
 (ht' : Nonempty (Derivation body Delta (graph1 InternalUnpair.left otherType output))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ output)) := by
 have hc := keyType p H G W input common typ parameter hd hk ht
 have hc' := keyType p H G W output common otherType parameter ho hk' ht'
 have he := valueUnique InternalUnpair.left otherType typ (Fin.cons common Fin.elim0) hc' hc
 exact outputTransport InternalUnpair.left otherType typ (Fin.cons output Fin.elim0) he ht'

theorem acceptedType (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input output typ parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W input parameter)))
 (ha : Nonempty (Derivation body Delta (OriginalAllPositionMinimumCoherenceTargets.Accepted
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P input output parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input))) :
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ output)) := by
 let q := OriginalStructuralClassKeyDefinitions.inputs p H G W
 let K := OriginalStructuralClassKeyDefinitions.key p H G W
 have ho := OriginalAllPositionAcceptedProof.actualHitDomain q H G W P body alpha Delta input output parameter hd ha
 have hm := OriginalActiveClassKernelBranchProof.matrixFromRelation q H G W
   OriginalRawSyntaxTransport.variableRankPackedRaw P input output parameter hd
   (andLeft (OriginalAllPositionAcceptedProof.acceptedRecover q H G W P input output parameter hd ha))
 have hk := andLeft (andRight hm)
 let qs : Fin 2 → Program 3 := ![.composition K ![.projection 0,.projection 2],leftOf (.projection 1)]
 let xs : Fin 3 → OTerm alpha := ![input,output,parameter]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs _
 intro beta j Theta ys hj hg
 let xx : Fin 3 → OTerm beta := ![input.relabel j,output.relabel j,parameter.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hx] at hg
 have hd' := renameInto hd j Theta hj
 have ho' := renameInto ho j Theta hj
 have hk' := renameInto hk j Theta hj
 have ht' := renameInto ht j Theta hj
 rw [OriginalActiveKernelMinimumSupportProof.domainRename] at hd' ho'
 rw [OriginalActiveClassKernelEqualityProof.keyGraphRename] at hk'
 rw [graph1Rename] at ht' ⊢
 have hki := binaryRecover K (.projection 0) (.projection 2) (ys 0)
   (input.relabel j) (parameter.relabel j) xx (hg 0) (projectionValue 0 xx) (projectionValue 2 xx)
 have hko := OriginalActiveClassKernelEqualityProof.keyTransfer K _ _ _ _ hk' hki
 have hty := unaryRecover InternalUnpair.left (.projection 1) (ys 1) (output.relabel j) xx (hg 1) (projectionValue 1 xx)
 exact sharedType p H G W (input.relabel j) (output.relabel j) (ys 0) (typ.relabel j) (ys 1)
   (parameter.relabel j) hd' ho' hki hko ht' hty
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherTypeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherTypeProof
