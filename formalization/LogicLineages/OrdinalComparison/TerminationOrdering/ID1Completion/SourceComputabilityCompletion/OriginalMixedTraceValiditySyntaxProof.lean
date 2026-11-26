module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValiditySyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedTraceValidityDefinitions
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open InternalStrongInduction

open OriginalContextInsertionSyntaxProof (insertSubst)
open OriginalLambdaErasureSquareDichotomySyntaxProof (witnessSubst)
open OriginalTypedDecoderInternalLogicSyntaxProof (orSubst)

theorem resultSubst {alpha beta : Type} (source : Program 2) (leaf : Program 4)
 (t oldParam : OTerm alpha) (ts : alpha → OTerm beta) :
 (result source leaf t oldParam).subst (fun a => emb (ts a)) =
 result source leaf (t.subst ts) (oldParam.subst ts) := by
 simp only [result,
  graph1,graph2,programSubst,consTermSubst,emptySubst,numeral,zSubst,sucSubst]

theorem fieldsSubst {alpha beta : Type} (source : Program 2) (leaf : Program 4)
 (path s t cert oldParam : OTerm alpha) (ts : alpha → OTerm beta) :
 (fields source leaf path s t cert oldParam ).subst (fun a => emb (ts a)) =
 fields source leaf (path.subst ts) (s.subst ts) (t.subst ts) (cert.subst ts) (oldParam.subst ts) := by
 simp only [fields,conjunctionSubst,insertSubst,graph1,graph2,graph3,graph4,programSubst,
  consTermSubst,emptySubst,numeral,zSubst,sucSubst]

theorem resultRename {alpha beta : Type} (source : Program 2) (leaf : Program 4)
 (t oldParam : OTerm alpha) (j : alpha → beta) :
 (result source leaf t oldParam).relabel j =
 result source leaf (t.relabel j) (oldParam.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (result source leaf t oldParam).subst (fun a => emb (.var (j a))) = _
 rw [resultSubst]
 simp only [← termRelabelAsSubst]

theorem fieldsRename {alpha beta : Type} (source : Program 2) (leaf : Program 4)
 (path s t cert oldParam : OTerm alpha) (j : alpha → beta) :
 (fields source leaf path s t cert oldParam ).relabel j =
 fields source leaf (path.relabel j) (s.relabel j) (t.relabel j) (cert.relabel j) (oldParam.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (fields source leaf path s t cert oldParam ).subst (fun a => emb (.var (j a))) = _
 rw [fieldsSubst]
 simp only [← termRelabelAsSubst]

theorem atPathSubst {alpha beta : Type} (source : Program 2) (leaf : Program 4)
 (path : OTerm alpha) (ts : alpha → OTerm beta) :
 (AtPath source leaf path).subst (fun a => emb (ts a)) = AtPath source leaf (path.subst ts) := by
 unfold AtPath matrix
 rw [allBlockSubst,liftedEmbedding]
 simp only [impSubst,fieldsSubst,resultSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atPathRename {alpha beta : Type} (source : Program 2) (leaf : Program 4)
 (path : OTerm alpha) (j : alpha → beta) :
 (AtPath source leaf path).relabel j = AtPath source leaf (path.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (AtPath source leaf path).subst (fun a => emb (.var (j a))) = _
 rw [atPathSubst]
 simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (source : Program 2) (leaf : Program 4)
 (path s t cert oldParam : OTerm alpha) :
 (matrix source leaf path).subst
  (Sum.elim Term.var (fun k => emb (![s,t,cert,oldParam] k))) =
 (fields source leaf path s t cert oldParam ).imp
  (result source leaf t oldParam) := by
 have he : (Sum.elim Term.var (fun k => emb (![s,t,cert,oldParam] k))) =
  (fun x => emb (Sum.elim Term.var ![s,t,cert,oldParam] x)) := by
  funext x
  cases x <;> rfl
 unfold matrix
 rw [he]
 simp only [impSubst,fieldsSubst,resultSubst,witnessLift,Term.subst,Sum.elim_inr]
 all_goals rfl

theorem pathPredicateInstantiate {alpha : Type} (source : Program 2) (leaf : Program 4) (path : OTerm alpha) :
 instantiate (pathPredicate source leaf) (emb path) = AtPath source leaf path := by
 rw [pathPredicate,instantiate,bindEmbedding,atPathSubst]
 simp only [varBind]

@[simp] theorem belowPathRename {alpha beta : Type} (source : Program 2) (leaf : Program 4)
 (path : OTerm alpha) (j : alpha → beta) :
 (BelowPath source leaf path).relabel j = BelowPath source leaf (path.relabel j) := by
 unfold BelowPath
 rw [InternalStrongInductionSyntaxProof.belowRename]
 unfold pathPredicate
 rw [atPathRename]
 rfl

theorem pathPredicateLift {alpha : Type} (source : Program 2) (leaf : Program 4) :
 lift (pathPredicate source leaf (alpha := alpha)) = pathPredicate source leaf (alpha := alpha ⊕ Fin 1) := by
 unfold lift pathPredicate
 rw [atPathRename]
 rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValiditySyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValiditySyntaxProof
