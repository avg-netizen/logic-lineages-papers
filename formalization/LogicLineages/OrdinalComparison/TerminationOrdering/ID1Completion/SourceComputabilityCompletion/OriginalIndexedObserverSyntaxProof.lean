module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverRangeSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalLambdaTraversalSelection OriginalIndexedObserverDefinitions
open OriginalIndexedObserverRangeSyntaxProof (rangeSubst rangeRename)
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
theorem observerIffSubst {α β : Type} (observer : Program 3)
    (out input parameter value cutoff : OrdinaryArithmetic.Term α) (ts : α → OrdinaryArithmetic.Term β) :
    (((graph3 observer value cutoff out parameter).iff (graph3 observer value cutoff input parameter))).subst (fun a => emb (ts a)) =
      ((graph3 observer (value.subst ts) (cutoff.subst ts) (out.subst ts) (parameter.subst ts)).iff
        (graph3 observer (value.subst ts) (cutoff.subst ts) (input.subst ts) (parameter.subst ts))) := by
  change ((graph3 observer value cutoff out parameter).subst (fun a => emb (ts a))).iff
    ((graph3 observer value cutoff input parameter).subst (fun a => emb (ts a))) = _
  simp only [graph3,programSubst,consTermSubst,emptySubst]

theorem observationsSubst {α β : Type} (K : Program 3) (out input parameter value cutoff : OrdinaryArithmetic.Term α)
    (ts : α → OrdinaryArithmetic.Term β) :
    (observations K out input parameter value cutoff).subst (fun a => emb (ts a)) =
      observations K (out.subst ts) (input.subst ts) (parameter.subst ts) (value.subst ts) (cutoff.subst ts) := by
  simp only [observations,conjunctionSubst,observerIffSubst]

theorem premisesSubst {α β : Type} (data : Data) (window : Program 1)
    (out input typ parameter : OrdinaryArithmetic.Term α) (ts : α → OrdinaryArithmetic.Term β) :
    (premises data window out input typ parameter).subst (fun a => emb (ts a)) =
      premises data window (out.subst ts) (input.subst ts) (typ.subst ts) (parameter.subst ts) := by
  simp only [premises,OriginalLambdaTraversalOutput.premises,OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    conjunctionSubst,
    InternalParameterizedCanonicalResultFoldSyntaxProof.sourcePremisesSubst,
    graph2,programSubst,consTermSubst,emptySubst,InternalOriginalStepGuard.one,sucSubst,zSubst]

@[simp] theorem observationsRename {α β : Type} (K : Program 3) (out input parameter value cutoff : OrdinaryArithmetic.Term α) (j : α → β) :
    (observations K out input parameter value cutoff).relabel j =
      observations K (out.relabel j) (input.relabel j) (parameter.relabel j) (value.relabel j) (cutoff.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (observations K out input parameter value cutoff).subst (fun a => emb (.var (j a))) = _
  rw [observationsSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem premisesRename {α β : Type} (data : Data) (window : Program 1)
    (out input typ parameter : OrdinaryArithmetic.Term α) (j : α → β) :
    (premises data window out input typ parameter).relabel j =
      premises data window (out.relabel j) (input.relabel j) (typ.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (premises data window out input typ parameter).subst (fun a => emb (.var (j a))) = _
  rw [premisesSubst]
  simp only [← termRelabelAsSubst]

theorem atPayloadSubst {α β : Type} (data : Data) (window : Program 1) (K : Program 3)
    (payload : OrdinaryArithmetic.Term α) (ts : α → OrdinaryArithmetic.Term β) :
    (atPayload data window K payload).subst (fun a => emb (ts a)) =
      atPayload data window K (payload.subst ts) := by
  unfold atPayload payloadMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    premisesSubst,rangeSubst,observationsSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atPayloadRename {α β : Type} (data : Data) (window : Program 1) (K : Program 3)
    (payload : OrdinaryArithmetic.Term α) (j : α → β) :
    (atPayload data window K payload).relabel j = atPayload data window K (payload.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (atPayload data window K payload).subst (fun a => emb (.var (j a))) = _
  rw [atPayloadSubst]
  simp only [← termRelabelAsSubst]

/-- Instantiate all six internal variables, including output and observer value. -/
theorem payloadMatrixWitness {α : Type} (data : Data) (window : Program 1) (K : Program 3)
    (payload input typ out parameter value cutoff : OrdinaryArithmetic.Term α) :
    (payloadMatrix data window K payload).subst
      (Sum.elim Term.var (fun i => emb (![input,typ,out,parameter,value,cutoff] i))) =
      (graph1 InternalUnpair.right payload input).imp
        ((premises data window out input typ parameter).imp
          ((ActualRange cutoff parameter).imp (observations K out input parameter value cutoff))) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,typ,out,parameter,value,cutoff] i))) =
      (fun a => emb (Sum.elim Term.var ![input,typ,out,parameter,value,cutoff] a)) := by
    funext a
    cases a <;> rfl
  unfold payloadMatrix
  rw [he]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    premisesSubst,rangeSubst,observationsSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem payloadPredicateInstantiate {α : Type} (data : Data) (window : Program 1) (K : Program 3)
    (payload : OrdinaryArithmetic.Term α) :
    instantiate (payloadPredicate data window K) (emb payload) = atPayload data window K payload := by
  rw [payloadPredicate,instantiate,bindEmbedding,atPayloadSubst]
  simp only [varBind]

@[simp] theorem belowPayloadRename {α β : Type} (data : Data) (window : Program 1) (K : Program 3)
    (payload : OrdinaryArithmetic.Term α) (j : α → β) :
    (belowPayload data window K payload).relabel j = belowPayload data window K (payload.relabel j) := by
  unfold belowPayload
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold payloadPredicate
  rw [atPayloadRename]
  rfl

theorem payloadPredicateLift {α : Type} (data : Data) (window : Program 1) (K : Program 3) :
    lift (payloadPredicate data window K (alpha := α)) =
      payloadPredicate data window K (alpha := α ⊕ Fin 1) := by
  unfold lift payloadPredicate
  rw [atPayloadRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverSyntaxProof
