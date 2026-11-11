module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalFullFoldSpine
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

theorem conclusionSubst {alpha beta : Type} (out input mark : OrdinaryArithmetic.Term alpha)
    (ts : alpha → OrdinaryArithmetic.Term beta) :
    (conclusion out input mark).subst (fun a => emb (ts a)) =
      conclusion (out.subst ts) (input.subst ts) (mark.subst ts) := by
  change ((BottomSpineMeasure.graph mark out).subst (fun a => emb (ts a))).iff
    ((BottomSpineMeasure.graph mark input).subst (fun a => emb (ts a))) = _
  simp only [conclusion,BottomSpineMeasure.graph,graph1,programSubst,consTermSubst,emptySubst]

theorem premisesSubst {alpha beta : Type} (data : Data) (window : Program 1)
    (out input typ parameter : OrdinaryArithmetic.Term alpha)
    (ts : alpha → OrdinaryArithmetic.Term beta) :
    (premises data window out input typ parameter).subst (fun a => emb (ts a)) =
      premises data window (out.subst ts) (input.subst ts) (typ.subst ts) (parameter.subst ts) := by
  simp only [premises,OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    conjunctionSubst,
    InternalParameterizedCanonicalResultFoldSyntaxProof.sourcePremisesSubst,
    InternalParameterizedCanonicalResultFoldSyntaxProof.foldGraphSubst,
    graph2,programSubst,consTermSubst,emptySubst,InternalOriginalStepGuard.one,sucSubst,zSubst]

@[simp] theorem conclusionRename {alpha beta : Type}
    (out input mark : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
    (conclusion out input mark).relabel j =
      conclusion (out.relabel j) (input.relabel j) (mark.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (conclusion out input mark).subst (fun a => emb (.var (j a))) = _
  rw [conclusionSubst]
  simp only [← termRelabelAsSubst]

@[simp] theorem premisesRename {alpha beta : Type} (data : Data) (window : Program 1)
    (out input typ parameter : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
    (premises data window out input typ parameter).relabel j =
      premises data window (out.relabel j) (input.relabel j) (typ.relabel j) (parameter.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (premises data window out input typ parameter).subst (fun a => emb (.var (j a))) = _
  rw [premisesSubst]
  simp only [← termRelabelAsSubst]

theorem atPayloadSubst {alpha beta : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term alpha) (ts : alpha → OrdinaryArithmetic.Term beta) :
    (atPayload data window payload).subst (fun a => emb (ts a)) =
      atPayload data window (payload.subst ts) := by
  unfold atPayload payloadMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    premisesSubst,conclusionSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atPayloadRename {alpha beta : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
    (atPayload data window payload).relabel j = atPayload data window (payload.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (atPayload data window payload).subst (fun a => emb (.var (j a))) = _
  rw [atPayloadSubst]
  simp only [← termRelabelAsSubst]

/-- Substitute all five variables while retaining the original payload graph. -/
theorem payloadMatrixWitness {alpha : Type} (data : Data) (window : Program 1)
    (payload input typ out parameter mark : OrdinaryArithmetic.Term alpha) :
    (payloadMatrix data window payload).subst
      (Sum.elim Term.var (fun i => emb (![input,typ,out,parameter,mark] i))) =
      (graph1 InternalUnpair.right payload input).imp
        ((premises data window out input typ parameter).imp
          (conclusion out input mark)) := by
  have he : (Sum.elim Term.var (fun i => emb (![input,typ,out,parameter,mark] i))) =
      (fun a => emb (Sum.elim Term.var ![input,typ,out,parameter,mark] a)) := by
    funext a
    cases a <;> rfl
  unfold payloadMatrix
  rw [he]
  simp only [impSubst,graph1,programSubst,consTermSubst,emptySubst,
    premisesSubst,conclusionSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem payloadPredicateInstantiate {alpha : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term alpha) :
    instantiate (payloadPredicate data window) (emb payload) = atPayload data window payload := by
  rw [payloadPredicate,instantiate,bindEmbedding,atPayloadSubst]
  simp only [varBind]

@[simp] theorem belowPayloadRename {alpha beta : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term alpha) (j : alpha → beta) :
    (belowPayload data window payload).relabel j = belowPayload data window (payload.relabel j) := by
  unfold belowPayload
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold payloadPredicate
  rw [atPayloadRename]
  rfl

theorem payloadPredicateLift {alpha : Type} (data : Data) (window : Program 1) :
    lift (payloadPredicate data window (alpha := alpha)) =
      payloadPredicate data window (alpha := alpha ⊕ Fin 1) := by
  unfold lift payloadPredicate
  rw [atPayloadRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineSyntaxProof
