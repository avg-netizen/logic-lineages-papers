module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceInductionSyntaxProof
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
open OriginalMixedDirectBottomTraceInductionDefinitions
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open InternalStrongInduction

open OriginalContextInsertionSyntaxProof (insertSubst)
open OriginalLambdaErasureSquareDichotomySyntaxProof (witnessSubst)
open OriginalTypedDecoderInternalLogicSyntaxProof (orSubst)

theorem resultSubst {alpha beta : Type} (source : Program 2) (leaf : Program 4)
 (s t newParam erasedS erasedT : OTerm alpha) (ts : alpha → OTerm beta) :
 (result source leaf s t newParam erasedS erasedT).subst (fun a => emb (ts a)) =
 result source leaf (s.subst ts) (t.subst ts) (newParam.subst ts) (erasedS.subst ts) (erasedT.subst ts) := by
 simp only [result,OriginalExistentialRankResultDefinitions.Result,OriginalExistentialRankResultSyntaxProof.rankSubst,
  conjunctionSubst,orSubst,equalSubst,witnessSubst,InternalLessThan.strictLess,orderSubst,
  graph1,graph2,programSubst,consTermSubst,emptySubst,numeral,zSubst,sucSubst]

theorem fieldsSubst {alpha beta : Type} (source : Program 2) (leaf : Program 4)
 (path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha) (ts : alpha → OTerm beta) :
 (fields source leaf path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT).subst (fun a => emb (ts a)) =
 fields source leaf (path.subst ts) (s.subst ts) (t.subst ts) (cert.subst ts) (oldParam.subst ts) (newParam.subst ts)
  (gamma.subst ts) (extended.subst ts) (d.subst ts) (cutoff.subst ts) (c.subst ts) (erasedS.subst ts) (erasedT.subst ts) := by
 simp only [fields,conjunctionSubst,insertSubst,graph1,graph2,graph3,graph4,programSubst,
  consTermSubst,emptySubst,numeral,zSubst,sucSubst]

theorem resultRename {alpha beta : Type} (source : Program 2) (leaf : Program 4)
 (s t newParam erasedS erasedT : OTerm alpha) (j : alpha → beta) :
 (result source leaf s t newParam erasedS erasedT).relabel j =
 result source leaf (s.relabel j) (t.relabel j) (newParam.relabel j) (erasedS.relabel j) (erasedT.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (result source leaf s t newParam erasedS erasedT).subst (fun a => emb (.var (j a))) = _
 rw [resultSubst]
 simp only [← termRelabelAsSubst]

theorem fieldsRename {alpha beta : Type} (source : Program 2) (leaf : Program 4)
 (path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha) (j : alpha → beta) :
 (fields source leaf path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT).relabel j =
 fields source leaf (path.relabel j) (s.relabel j) (t.relabel j) (cert.relabel j) (oldParam.relabel j) (newParam.relabel j)
  (gamma.relabel j) (extended.relabel j) (d.relabel j) (cutoff.relabel j) (c.relabel j) (erasedS.relabel j) (erasedT.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (fields source leaf path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT).subst (fun a => emb (.var (j a))) = _
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
 (path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha) :
 (matrix source leaf path).subst
  (Sum.elim Term.var (fun k => emb (![s,t,cert,oldParam,newParam,gamma,extended,d,cutoff,c,erasedS,erasedT] k))) =
 (fields source leaf path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT).imp
  (result source leaf s t newParam erasedS erasedT) := by
 have he : (Sum.elim Term.var (fun k => emb (![s,t,cert,oldParam,newParam,gamma,extended,d,cutoff,c,erasedS,erasedT] k))) =
  (fun x => emb (Sum.elim Term.var ![s,t,cert,oldParam,newParam,gamma,extended,d,cutoff,c,erasedS,erasedT] x)) := by
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
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceInductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceInductionSyntaxProof
