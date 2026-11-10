module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalApplicationSidecar OriginalApplicationSidecarSpine
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalStrongInduction SourceComputabilityFormulaSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem conclusionSubst {α β : Type} (out input value : OrdinaryArithmetic.Term α)
    (ts : α → OrdinaryArithmetic.Term β) :
    (conclusion out input value).subst (fun a => emb (ts a)) =
      conclusion (out.subst ts) (input.subst ts) (value.subst ts) := by
  change ((BottomSpineMeasure.graph value out).subst (fun a => emb (ts a))).iff
    ((BottomSpineMeasure.graph value input).subst (fun a => emb (ts a))) = _
  simp only [conclusion,BottomSpineMeasure.graph,graph1,programSubst,consTermSubst,emptySubst]

theorem premisesSubst {α β : Type} (data : Data) (window : Program 1)
    (out input typ parameter : OrdinaryArithmetic.Term α) (ts : α → OrdinaryArithmetic.Term β) :
    (premises data window out input typ parameter).subst (fun a => emb (ts a)) =
      premises data window (out.subst ts) (input.subst ts) (typ.subst ts) (parameter.subst ts) := by
  simp only [premises,OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    conjunctionSubst,
    InternalParameterizedCanonicalResultFoldSyntaxProof.sourcePremisesSubst,
    graph2,programSubst,consTermSubst,emptySubst,InternalOriginalStepGuard.one,sucSubst,zSubst]

@[simp] theorem conclusionRename {α β : Type} (out input value : OrdinaryArithmetic.Term α) (j : α → β) :
    (conclusion out input value).relabel j =
      conclusion (out.relabel j) (input.relabel j) (value.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (conclusion out input value).subst (fun a => emb (.var (j a))) = _
  rw [conclusionSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem premisesRename {α β : Type} (data : Data) (window : Program 1)
    (out input typ parameter : OrdinaryArithmetic.Term α) (j : α → β) :
    (premises data window out input typ parameter).relabel j =
      premises data window (out.relabel j) (input.relabel j) (typ.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (premises data window out input typ parameter).subst (fun a => emb (.var (j a))) = _
  rw [premisesSubst]
  simp only [← termRelabelAsSubst]

theorem atPayloadSubst {α β : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term α) (ts : α → OrdinaryArithmetic.Term β) :
    (atPayload data window payload).subst (fun a => emb (ts a)) =
      atPayload data window (payload.subst ts) := by
  unfold atPayload payloadMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    premisesSubst,conclusionSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atPayloadRename {α β : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term α) (j : α → β) :
    (atPayload data window payload).relabel j = atPayload data window (payload.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (atPayload data window payload).subst (fun a => emb (.var (j a))) = _
  rw [atPayloadSubst]
  simp only [← termRelabelAsSubst]

/-- Instantiate all five internal variables, including output and observer value. -/
theorem payloadMatrixWitness {α : Type} (data : Data) (window : Program 1)
    (payload input typ out parameter value : OrdinaryArithmetic.Term α) :
    (payloadMatrix data window payload).subst
      (Sum.elim Term.var (fun i => emb (![input,typ,out,parameter,value] i))) =
      (graph1 InternalUnpair.right payload input).imp
        ((premises data window out input typ parameter).imp
          (conclusion out input value)) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,typ,out,parameter,value] i))) =
      (fun a => emb (Sum.elim Term.var ![input,typ,out,parameter,value] a)) := by
    funext a
    cases a <;> rfl
  unfold payloadMatrix
  rw [he]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    premisesSubst,conclusionSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem payloadPredicateInstantiate {α : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term α) :
    instantiate (payloadPredicate data window) (emb payload) = atPayload data window payload := by
  rw [payloadPredicate,instantiate,bindEmbedding,atPayloadSubst]
  simp only [varBind]

@[simp] theorem belowPayloadRename {α β : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term α) (j : α → β) :
    (belowPayload data window payload).relabel j = belowPayload data window (payload.relabel j) := by
  unfold belowPayload
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold payloadPredicate
  rw [atPayloadRename]
  rfl

theorem payloadPredicateLift {α : Type} (data : Data) (window : Program 1) :
    lift (payloadPredicate data window (alpha := α)) =
      payloadPredicate data window (alpha := α ⊕ Fin 1) := by
  unfold lift payloadPredicate
  rw [atPayloadRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineSyntaxProof
