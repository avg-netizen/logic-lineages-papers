module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeIterationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeIterationSyntaxProof
open OriginalVariableRepresentative
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityCompletion.OriginalVariableRepresentativeIteration
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

@[simp] theorem activeSubst {α β : Type} (data : Data) (window : Program 1)
    (input parameter : OTerm α) (ts : α → OTerm β) :
    (activeGraph data window input parameter).subst (fun a => emb (ts a)) =
      activeGraph data window (input.subst ts) (parameter.subst ts) := by
  simp only [activeGraph,BottomRepresentative.activeGraph,graph2,programSubst,consTermSubst,emptySubst,
    InternalOriginalStepGuard.one,sucSubst,zSubst]

@[simp] theorem activeRename {α β : Type} (data : Data) (window : Program 1)
    (input parameter : OTerm α) (j : α → β) :
    (activeGraph data window input parameter).relabel j =
      activeGraph data window (input.relabel j) (parameter.relabel j) := by
  simp only [activeGraph,BottomRepresentative.activeGraph,graph2Rename,sucRelabel,zRelabel,InternalOriginalStepGuard.one]

@[simp] theorem markSubst {α β : Type} (indicator input : OTerm α) (ts : α → OTerm β) :
    (markGraph indicator input).subst (fun a => emb (ts a)) =
      markGraph (indicator.subst ts) (input.subst ts) := by
  simp only [markGraph,graph1,programSubst,consTermSubst,emptySubst]

@[simp] theorem markRename {α β : Type} (indicator input : OTerm α) (j : α → β) :
    (markGraph indicator input).relabel j =
      markGraph (indicator.relabel j) (input.relabel j) := by
  simp only [markGraph,graph1Rename]


theorem rowSubst {α β : Type} (data : Data) (window : Program 1)
    (count : OTerm α) (ts : α → OTerm β) :
    (iterationRow data window count).subst (fun a => emb (ts a)) =
      iterationRow data window (count.subst ts) := by
  unfold OriginalVariableRepresentativeIteration.iterationRow OriginalVariableRepresentativeIteration.iterationBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [conjunctionSubst,repeatSubst,activeSubst,markSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem rowRename {α β : Type} (data : Data) (window : Program 1)
    (count : OTerm α) (j : α → β) :
    (iterationRow data window count).relabel j = iterationRow data window (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (iterationRow data window count).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem bodyWitness {α : Type} (data : Data) (window : Program 1)
    (count input out parameter indicator : OTerm α) :
    (iterationBody data window count).subst
      (Sum.elim Term.var (fun i => emb (![input,out,parameter,indicator] i))) =
      (InternalParameterizedNumericIteration.repeatGraph (step data window) out count input parameter ⊓
        (activeGraph data window input parameter ⊓ markGraph indicator input)).imp
        (markGraph indicator out) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,out,parameter,indicator] i))) =
      (fun a => emb (Sum.elim Term.var ![input,out,parameter,indicator] a)) := by
    funext a
    cases a <;> rfl
  unfold OriginalVariableRepresentativeIteration.iterationBody
  rw [he,impSubst]
  simp only [conjunctionSubst,repeatSubst,activeSubst,markSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rowInstantiate {α : Type} (data : Data) (window : Program 1)
    (count : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (iterationRow data window count) (emb t) =
      iterationRow data window (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]

theorem rowSuccessor {α : Type} (data : Data) (window : Program 1)
    (count : OTerm (α ⊕ Fin 1)) :
    successorInstance (iterationRow data window count) =
      iterationRow data window (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeIterationSyntaxProof
