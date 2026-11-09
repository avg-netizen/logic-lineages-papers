module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityCompletion.BottomRepresentative SourceComputabilityCompletion.BottomDescent
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalParameterizedBoundedDescentNormalizerSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalClosedPrograms InternalClosedProgramsBindingProof InternalRawListRecursionSyntaxProof
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem selectedValidity_eq (data : Data) (window : Program 1) :
    selectedValidity data window = InternalOriginalUniformDescentSelection.validity
      (InternalOriginalUniformContextMembership.normalizeData data) := rfl

@[simp] theorem activeSubst {α β : Type} (data : Data) (window : Program 1)
    (input parameter : OTerm α) (ts : α → OTerm β) :
    (activeGraph data window input parameter).subst (fun a => emb (ts a)) =
      activeGraph data window (input.subst ts) (parameter.subst ts) := by
  simp only [activeGraph,graph2,programSubst,consTermSubst,emptySubst,
    InternalOriginalStepGuard.one,sucSubst,zSubst]

@[simp] theorem activeRename {α β : Type} (data : Data) (window : Program 1)
    (input parameter : OTerm α) (j : α → β) :
    (activeGraph data window input parameter).relabel j =
      activeGraph data window (input.relabel j) (parameter.relabel j) := by
  simp only [activeGraph,graph2Rename,sucRelabel,zRelabel,InternalOriginalStepGuard.one]

@[simp] theorem bottomSubst {α β : Type} (indicator input : OTerm α) (ts : α → OTerm β) :
    (bottomGraph indicator input).subst (fun a => emb (ts a)) =
      bottomGraph (indicator.subst ts) (input.subst ts) := by
  simp only [bottomGraph,graph1,programSubst,consTermSubst,emptySubst]

@[simp] theorem bottomRename {α β : Type} (indicator input : OTerm α) (j : α → β) :
    (bottomGraph indicator input).relabel j =
      bottomGraph (indicator.relabel j) (input.relabel j) := by
  simp only [bottomGraph,graph1Rename]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentSyntaxProof
