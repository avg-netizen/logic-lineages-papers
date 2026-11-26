module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationSelectedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyMinimumProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem minimumKeyIff (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (out input parameter mark : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain p H G W input parameter)))
    (hr : Nonempty (Derivation body Delta
      (graph2 (OriginalActiveKernelMinimum.inputs p H G W P).base.oldRepresentative out input parameter))) :
    Nonempty (Derivation body Delta
      ((graph2 p.base.oldRepresentative mark out parameter).iff
        (graph2 p.base.oldRepresentative mark input parameter))) := by
  have hhit := OriginalActiveKernelMinimumSupportProof.minimumHit p H G W P input out parameter hd hr
  have hm := OriginalActiveClassKernelBranchProof.matrixFromRelation p H G W
    OriginalRawSyntaxTransport.variableRankPackedRaw P input out parameter hd hhit
  have hk := andLeft (andRight hm)
  let K := p.base.oldRepresentative
  apply programCases K (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta value hj hg
  change Nonempty (Derivation body Theta
    (((graph2 K mark out parameter).relabel j).iff ((graph2 K mark input parameter).relabel j)))
  rw [graph2Rename,graph2Rename]
  have hk' := renameInto hk j Theta hj
  rw [OriginalActiveClassKernelEqualityProof.keyGraphRename] at hk'
  have hg' : Nonempty (Derivation body Theta (graph2 K value (input.relabel j) (parameter.relabel j))) := by
    simpa only [consTermRename,emptyRename] using hg
  have ho := OriginalActiveClassKernelEqualityProof.keyTransfer K
    (input.relabel j) (out.relabel j) (parameter.relabel j) value hk' hg'
  exact OriginalStructuralKeyIterationSelectedProof.indicatorIff K
    (mark.relabel j) (out.relabel j) (input.relabel j) value value (parameter.relabel j)
    ho hg' ⟨InternalTagArithmeticSupportProof.refl value⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyMinimumProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyMinimumProof
