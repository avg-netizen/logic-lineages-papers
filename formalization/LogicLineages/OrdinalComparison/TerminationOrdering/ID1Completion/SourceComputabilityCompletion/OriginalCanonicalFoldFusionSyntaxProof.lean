module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalCanonicalFoldFusion
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
theorem outputInvariantSubst {α β : Type} (data : Data) (window : Program 1) (source target : Program 2)
    (out input typ parameter : OrdinaryArithmetic.Term α) (ts : α → OrdinaryArithmetic.Term β) :
    (outputInvariant data window source target out input typ parameter).subst (fun a => emb (ts a)) =
      outputInvariant data window source target (out.subst ts) (input.subst ts) (typ.subst ts) (parameter.subst ts) := by
  simp only [outputInvariant,graph2,programSubst,consTermSubst,emptySubst]

theorem premisesSubst {α β : Type} (data : Data) (window : Program 1) (source target : Program 2)
    (out input typ parameter : OrdinaryArithmetic.Term α) (ts : α → OrdinaryArithmetic.Term β) :
    (premises data window source target out input typ parameter).subst (fun a => emb (ts a)) =
      premises data window source target (out.subst ts) (input.subst ts) (typ.subst ts) (parameter.subst ts) := by
  simp only [premises,conjunctionSubst,OriginalFunctionNeutrality.windowGraph,
    OriginalVariableRepresentative.windowGraph,InternalOriginalStepGuard.one,sucSubst,zSubst,
    InternalParameterizedCanonicalResultFoldSyntaxProof.sourcePremisesSubst,
    graph2,programSubst,consTermSubst,emptySubst]

@[simp] theorem outputInvariantRename {α β : Type} (data : Data) (window : Program 1) (source target : Program 2)
    (out input typ parameter : OrdinaryArithmetic.Term α) (j : α → β) :
    (outputInvariant data window source target out input typ parameter).relabel j =
      outputInvariant data window source target (out.relabel j) (input.relabel j) (typ.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (outputInvariant data window source target out input typ parameter).subst (fun a => emb (.var (j a))) = _
  rw [outputInvariantSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem premisesRename {α β : Type} (data : Data) (window : Program 1) (source target : Program 2)
    (out input typ parameter : OrdinaryArithmetic.Term α) (j : α → β) :
    (premises data window source target out input typ parameter).relabel j =
      premises data window source target (out.relabel j) (input.relabel j) (typ.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (premises data window source target out input typ parameter).subst (fun a => emb (.var (j a))) = _
  rw [premisesSubst]
  simp only [← termRelabelAsSubst]

theorem atPayloadSubst {α β : Type} (data : Data) (window : Program 1) (source target : Program 2)
    (payload : OrdinaryArithmetic.Term α) (ts : α → OrdinaryArithmetic.Term β) :
    (atPayload data window source target payload).subst (fun a => emb (ts a)) =
      atPayload data window source target (payload.subst ts) := by
  unfold atPayload payloadMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    premisesSubst,outputInvariantSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atPayloadRename {α β : Type} (data : Data) (window : Program 1) (source target : Program 2)
    (payload : OrdinaryArithmetic.Term α) (j : α → β) :
    (atPayload data window source target payload).relabel j = atPayload data window source target (payload.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (atPayload data window source target payload).subst (fun a => emb (.var (j a))) = _
  rw [atPayloadSubst]
  simp only [← termRelabelAsSubst]

/-- Instantiate all four internal variables, including the actual output. -/
theorem payloadMatrixWitness {α : Type} (data : Data) (window : Program 1) (source target : Program 2)
    (payload input typ out parameter : OrdinaryArithmetic.Term α) :
    (payloadMatrix data window source target payload).subst
      (Sum.elim Term.var (fun i => emb (![input,typ,out,parameter] i))) =
      (graph1 InternalUnpair.right payload input).imp
        ((premises data window source target out input typ parameter).imp
          (outputInvariant data window source target out input typ parameter)) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,typ,out,parameter] i))) =
      (fun a => emb (Sum.elim Term.var ![input,typ,out,parameter] a)) := by
    funext a
    cases a <;> rfl
  unfold payloadMatrix
  rw [he]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    premisesSubst,outputInvariantSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem payloadPredicateInstantiate {α : Type} (data : Data) (window : Program 1) (source target : Program 2)
    (payload : OrdinaryArithmetic.Term α) :
    instantiate (payloadPredicate data window source target) (emb payload) = atPayload data window source target payload := by
  rw [payloadPredicate,instantiate,bindEmbedding,atPayloadSubst]
  simp only [varBind]

@[simp] theorem belowPayloadRename {α β : Type} (data : Data) (window : Program 1) (source target : Program 2)
    (payload : OrdinaryArithmetic.Term α) (j : α → β) :
    (belowPayload data window source target payload).relabel j = belowPayload data window source target (payload.relabel j) := by
  unfold belowPayload
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold payloadPredicate
  rw [atPayloadRename]
  rfl

theorem payloadPredicateLift {α : Type} (data : Data) (window : Program 1) (source target : Program 2) :
    lift (payloadPredicate data window source target (alpha := α)) =
      payloadPredicate data window source target (alpha := α ⊕ Fin 1) := by
  unfold lift payloadPredicate
  rw [atPayloadRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalFoldFusionSyntaxProof
