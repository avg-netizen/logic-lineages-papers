module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportSyntaxProof
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
open OriginalRawVariableRankTransport OriginalRawSyntaxTransport
open InternalStrongInduction

open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof

theorem rankRelationSubst {alpha beta : Type} (erasing : Bool)
    (after before : OTerm alpha) (ts : alpha → OTerm beta) :
    (RankRelation erasing after before).subst (fun a => emb (ts a)) =
      RankRelation erasing (after.subst ts) (before.subst ts) := by
  cases erasing <;> simp only [RankRelation,Bool.false_eq_true,if_false,if_true,
    equalEqn,eqnSubst,InternalLessThan.strictLess,orderSubst,sucSubst]

@[simp] theorem rankRelationRename {alpha beta : Type} (erasing : Bool)
    (after before : OTerm alpha) (j : alpha → beta) :
    (RankRelation erasing after before).relabel j =
      RankRelation erasing (after.relabel j) (before.relabel j) := by
  cases erasing <;> simp only [RankRelation,Bool.false_eq_true,if_false,if_true,
    equalEqn,eqnRelabel,InternalLessThan.strictLess,orderRename,sucRelabel]

theorem atRawSubst {alpha beta : Type} (p : Program 3) (erasing : Bool)
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw p erasing raw).subst (fun a => emb (ts a)) = AtRaw p erasing (raw.subst ts) := by
  unfold AtRaw transportMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,graph3,graph1,programSubst,rankRelationSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename {alpha beta : Type} (p : Program 3) (erasing : Bool)
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw p erasing raw).relabel j = AtRaw p erasing (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw p erasing raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem transportMatrixWitness {alpha : Type} (p : Program 3) (erasing : Bool)
    (raw d k transformed before after : OTerm alpha) :
    (transportMatrix p erasing raw).subst
      (Sum.elim Term.var (fun i => emb (![d,k,transformed,before,after] i))) =
      (graph3 p transformed d k raw ⊓
        (graph1 variableRankRaw before raw ⊓ graph1 variableRankRaw after transformed)).imp
        (RankRelation erasing after before) := by
  have he : (Sum.elim Term.var (fun i => emb (![d,k,transformed,before,after] i))) =
      (fun a => emb (Sum.elim Term.var ![d,k,transformed,before,after] a)) := by
    funext a
    cases a <;> rfl
  unfold transportMatrix
  rw [he]
  simp only [impSubst,conjunctionSubst,graph3,graph1,programSubst,rankRelationSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  all_goals rfl

theorem rawPredicateInstantiate {alpha : Type} (p : Program 3) (rank : Bool) (raw : OTerm alpha) :
    instantiate (rawPredicate p rank) (emb raw) = AtRaw p rank raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename {alpha beta : Type} (p : Program 3) (rank : Bool)
    (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw p rank raw).relabel j = BelowRaw p rank (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl

theorem rawPredicateLift {alpha : Type} (p : Program 3) (rank : Bool) :
    lift (rawPredicate p rank (alpha := alpha)) = rawPredicate p rank (alpha := alpha ⊕ Fin 1) := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportSyntaxProof
