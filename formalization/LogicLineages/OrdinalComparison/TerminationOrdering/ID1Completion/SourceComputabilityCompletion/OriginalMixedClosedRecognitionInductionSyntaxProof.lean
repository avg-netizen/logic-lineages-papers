module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionInductionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof (impSubst)
open InternalRawListRepeatSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedClosedRecognitionInductionDefinitions
open InternalStrongInduction

theorem fieldsSubst {alpha beta : Type} (source : Program 2) (leaf : Program 4)
 (path out state : OTerm alpha) (ts : alpha → OTerm beta) :
 (fields source leaf path out state).subst (fun a => emb (ts a)) =
 fields source leaf (path.subst ts) (out.subst ts) (state.subst ts) := by
 simp only [fields,conjunctionSubst,repeatSubst,graph1,programSubst,
  consTermSubst,emptySubst,sucSubst,zSubst]

theorem resultSubst {alpha beta : Type} (source : Program 2) (leaf : Program 4)
 (path out state : OTerm alpha) (ts : alpha → OTerm beta) :
 (result source leaf path out state).subst (fun a => emb (ts a)) =
 result source leaf (path.subst ts) (out.subst ts) (state.subst ts) := by
 simp only [result,conjunctionSubst,repeatSubst,graph1,programSubst,
  consTermSubst,emptySubst,sucSubst,zSubst]

theorem fieldsRename {alpha beta : Type} (source : Program 2) (leaf : Program 4)
 (path out state : OTerm alpha) (j : alpha → beta) :
 (fields source leaf path out state).relabel j =
 fields source leaf (path.relabel j) (out.relabel j) (state.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (fields source leaf path out state).subst (fun a => emb (.var (j a))) = _
 rw [fieldsSubst]
 simp only [← termRelabelAsSubst]

theorem resultRename {alpha beta : Type} (source : Program 2) (leaf : Program 4)
 (path out state : OTerm alpha) (j : alpha → beta) :
 (result source leaf path out state).relabel j =
 result source leaf (path.relabel j) (out.relabel j) (state.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (result source leaf path out state).subst (fun a => emb (.var (j a))) = _
 rw [resultSubst]
 simp only [← termRelabelAsSubst]

theorem atPathSubst {alpha beta : Type} (source : Program 2) (leaf outLeaf : Program 4)
 (path : OTerm alpha) (ts : alpha → OTerm beta) :
 (AtPath source leaf outLeaf path).subst (fun a => emb (ts a)) =
 AtPath source leaf outLeaf (path.subst ts) := by
 unfold AtPath matrix
 rw [allBlockSubst,liftedEmbedding]
 simp only [impSubst,fieldsSubst,resultSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atPathRename {alpha beta : Type} (source : Program 2) (leaf outLeaf : Program 4)
 (path : OTerm alpha) (j : alpha → beta) :
 (AtPath source leaf outLeaf path).relabel j = AtPath source leaf outLeaf (path.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (AtPath source leaf outLeaf path).subst (fun a => emb (.var (j a))) = _
 rw [atPathSubst]
 simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (source : Program 2) (leaf outLeaf : Program 4)
 (path out state : OTerm alpha) :
 (matrix source leaf outLeaf path).subst
  (Sum.elim Term.var (fun k => emb (![out,state] k))) =
 (fields source leaf path out state).imp (result source outLeaf path out state) := by
 have he : (Sum.elim Term.var (fun k => emb (![out,state] k))) =
  (fun x => emb (Sum.elim Term.var ![out,state] x)) := by
  funext x
  cases x <;> rfl
 unfold matrix
 rw [he]
 simp only [impSubst,fieldsSubst,resultSubst,witnessLift,Term.subst,Sum.elim_inr]
 all_goals rfl

theorem pathPredicateInstantiate {alpha : Type} (source : Program 2) (leaf outLeaf : Program 4)
 (path : OTerm alpha) :
 instantiate (pathPredicate source leaf outLeaf) (emb path) = AtPath source leaf outLeaf path := by
 rw [pathPredicate,instantiate,bindEmbedding,atPathSubst]
 simp only [varBind]

@[simp] theorem belowPathRename {alpha beta : Type} (source : Program 2) (leaf outLeaf : Program 4)
 (path : OTerm alpha) (j : alpha → beta) :
 (BelowPath source leaf outLeaf path).relabel j = BelowPath source leaf outLeaf (path.relabel j) := by
 unfold BelowPath
 rw [InternalStrongInductionSyntaxProof.belowRename]
 unfold pathPredicate
 rw [atPathRename]
 rfl

theorem pathPredicateLift {alpha : Type} (source : Program 2) (leaf outLeaf : Program 4) :
 lift (pathPredicate source leaf outLeaf (alpha := alpha)) =
 pathPredicate source leaf outLeaf (alpha := alpha ⊕ Fin 1) := by
 unfold lift pathPredicate
 rw [atPathRename]
 rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionInductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionInductionSyntaxProof
