module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityCompletion.OriginalStructuralKeyIteration
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

@[simp] theorem activeSubst {α β : Type} (data : Data)
    (input parameter : OTerm α) (ts : α → OTerm β) :
    (activeGraph data input parameter).subst (fun a => emb (ts a)) =
      activeGraph data (input.subst ts) (parameter.subst ts) := by
  simp only [activeGraph,graph2,programSubst,consTermSubst,emptySubst,
    InternalOriginalStepGuard.one,sucSubst,zSubst]

@[simp] theorem activeRename {α β : Type} (data : Data)
    (input parameter : OTerm α) (j : α → β) :
    (activeGraph data input parameter).relabel j =
      activeGraph data (input.relabel j) (parameter.relabel j) := by
  simp only [activeGraph,graph2Rename,sucRelabel,zRelabel,InternalOriginalStepGuard.one]

@[simp] theorem markSubst {α β : Type} (data : Data) (indicator input parameter : OTerm α) (ts : α → OTerm β) :
    (markGraph data indicator input parameter).subst (fun a => emb (ts a)) =
      markGraph data (indicator.subst ts) (input.subst ts) (parameter.subst ts) := by
  simp only [markGraph,graph2,programSubst,consTermSubst,emptySubst]

@[simp] theorem markRename {α β : Type} (data : Data) (indicator input parameter : OTerm α) (j : α → β) :
    (markGraph data indicator input parameter).relabel j =
      markGraph data (indicator.relabel j) (input.relabel j) (parameter.relabel j) := by
  simp only [markGraph,graph2Rename]


theorem rowSubst {α β : Type} (data : Data)
    (count : OTerm α) (ts : α → OTerm β) :
    (iterationRow data count).subst (fun a => emb (ts a)) =
      iterationRow data (count.subst ts) := by
  unfold OriginalStructuralKeyIteration.iterationRow OriginalStructuralKeyIteration.iterationBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [conjunctionSubst,repeatSubst,activeSubst,markSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem rowRename {α β : Type} (data : Data)
    (count : OTerm α) (j : α → β) :
    (iterationRow data count).relabel j = iterationRow data (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (iterationRow data count).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem bodyWitness {α : Type} (data : Data)
    (count input out parameter indicator : OTerm α) :
    (iterationBody data count).subst
      (Sum.elim Term.var (fun i => emb (![input,out,parameter,indicator] i))) =
      (InternalParameterizedNumericIteration.repeatGraph (step data) out count input parameter ⊓
        (activeGraph data input parameter ⊓ markGraph data indicator input parameter)).imp
        (markGraph data indicator out parameter) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,out,parameter,indicator] i))) =
      (fun a => emb (Sum.elim Term.var ![input,out,parameter,indicator] a)) := by
    funext a
    cases a <;> rfl
  unfold OriginalStructuralKeyIteration.iterationBody
  rw [he,impSubst]
  simp only [conjunctionSubst,repeatSubst,activeSubst,markSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rowInstantiate {α : Type} (data : Data)
    (count : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (iterationRow data count) (emb t) =
      iterationRow data (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]

theorem rowSuccessor {α : Type} (data : Data)
    (count : OTerm (α ⊕ Fin 1)) :
    successorInstance (iterationRow data count) =
      iterationRow data (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationSyntaxProof
