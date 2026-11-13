module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalInductionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open EvaluatorKeyCanonicalInductionDefinitions
open UniformCertificateCompletion
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
theorem premisesSubst {α β : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (left right leftOut rightOut parameter : OrdinaryArithmetic.Term α) (ts : α → OrdinaryArithmetic.Term β) :
 (Premises p H G W P left right leftOut rightOut parameter).subst (fun a => emb (ts a)) =
 Premises p H G W P (left.subst ts) (right.subst ts) (leftOut.subst ts) (rightOut.subst ts) (parameter.subst ts) := by
 simp only [Premises,EvaluatorKeyPut.Domain,OriginalActiveClassKernel.Domain,EvaluatorKeyPut.Same,
   conjunctionSubst,SixSol20261113.Erasure.EvaluatorErasureSyntax.sameSubst,
   graph2,programSubst,consTermSubst,emptySubst,InternalOriginalStepGuard.one,sucSubst,zSubst]
@[simp] theorem premisesRename {α β : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (left right leftOut rightOut parameter : OrdinaryArithmetic.Term α) (j : α → β) :
 (Premises p H G W P left right leftOut rightOut parameter).relabel j =
 Premises p H G W P (left.relabel j) (right.relabel j) (leftOut.relabel j) (rightOut.relabel j) (parameter.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Premises p H G W P left right leftOut rightOut parameter).subst (fun a => emb (.var (j a))) = _
 rw [premisesSubst]
 simp only [← termRelabelAsSubst]

theorem atPayloadSubst {α β : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (payload : OrdinaryArithmetic.Term α) (ts : α → OrdinaryArithmetic.Term β) :
    (atPayload p H G W P payload).subst (fun a => emb (ts a)) =
      atPayload p H G W P (payload.subst ts) := by
  unfold atPayload payloadMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    premisesSubst,OriginalTypedDecoderInternalLogicSyntaxProof.equalSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atPayloadRename {α β : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (payload : OrdinaryArithmetic.Term α) (j : α → β) :
    (atPayload p H G W P payload).relabel j = atPayload p H G W P (payload.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (atPayload p H G W P payload).subst (fun a => emb (.var (j a))) = _
  rw [atPayloadSubst]
  simp only [← termRelabelAsSubst]

/-- Instantiate all five internal variables, including output and observer value. -/
theorem payloadMatrixWitness {α : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (payload left right leftOut rightOut parameter : OrdinaryArithmetic.Term α) :
    (payloadMatrix p H G W P payload).subst
      (Sum.elim Term.var (fun i => emb (![left,right,leftOut,rightOut,parameter] i))) =
      (graph1 InternalUnpair.right payload left).imp
        ((Premises p H G W P left right leftOut rightOut parameter).imp
          (equal leftOut rightOut)) := by
  have he : (Sum.elim Term.var (fun i => emb (![left,right,leftOut,rightOut,parameter] i))) =
      (fun a => emb (Sum.elim Term.var ![left,right,leftOut,rightOut,parameter] a)) := by
    funext a
    cases a <;> rfl
  unfold payloadMatrix
  rw [he]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    premisesSubst,OriginalTypedDecoderInternalLogicSyntaxProof.equalSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem payloadPredicateInstantiate {α : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (payload : OrdinaryArithmetic.Term α) :
    instantiate (payloadPredicate p H G W P) (emb payload) = atPayload p H G W P payload := by
  rw [payloadPredicate,instantiate,bindEmbedding,atPayloadSubst]
  simp only [varBind]

@[simp] theorem belowPayloadRename {α β : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (payload : OrdinaryArithmetic.Term α) (j : α → β) :
    (belowPayload p H G W P payload).relabel j = belowPayload p H G W P (payload.relabel j) := by
  unfold belowPayload
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold payloadPredicate
  rw [atPayloadRename]
  rfl

theorem payloadPredicateLift {α : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) :
    lift (payloadPredicate p H G W P (alpha := α)) =
      payloadPredicate p H G W P (alpha := α ⊕ Fin 1) := by
  unfold lift payloadPredicate
  rw [atPayloadRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalSyntaxProof
