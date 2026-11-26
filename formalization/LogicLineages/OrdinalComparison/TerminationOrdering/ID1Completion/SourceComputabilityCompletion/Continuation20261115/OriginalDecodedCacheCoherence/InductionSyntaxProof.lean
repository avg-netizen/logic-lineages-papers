module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.InductionSyntaxProof
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
open InductionDefinitions
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open InternalStrongInduction
open OriginalContextInsertionSyntaxProof (lengthSubst)

theorem atRawSubst (n : Nat) (arity : Fin n → Nat) (V : Program 3) {alpha beta : Type} 
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw n arity V raw).subst (fun a => emb (ts a)) = AtRaw n arity V (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,equalSubst,fields,result,lengthSubst,notSubst,eqnSubst,graph2,graph3,programSubst,boundedSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename (n : Nat) (arity : Fin n → Nat) (V : Program 3) {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw n arity V raw).relabel j = AtRaw n arity V (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw n arity V raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (n : Nat) (arity : Fin n → Nat) (V : Program 3) {alpha : Type} (raw node param index1 seed1 rank1 depth1 frontier1 table1 index2 seed2 rank2 depth2 frontier2 table2 found : OTerm alpha) :
    (matrix n arity V raw).subst (Sum.elim Term.var (fun i => emb (![node,param,index1,seed1,rank1,depth1,frontier1,table1,index2,seed2,rank2,depth2,frontier2,table2,found] i))) =
      (fields n arity V raw node param index1 seed1 rank1 depth1 frontier1 table1 index2 seed2 rank2 depth2 frontier2 table2 found).imp (result raw node param index1 seed1 rank1 depth1 frontier1 table1 index2 seed2 rank2 depth2 frontier2 table2 found) := by
  have he : (Sum.elim Term.var (fun i => emb (![node,param,index1,seed1,rank1,depth1,frontier1,table1,index2,seed2,rank2,depth2,frontier2,table2,found] i))) =
      (fun a => emb (Sum.elim Term.var ![node,param,index1,seed1,rank1,depth1,frontier1,table1,index2,seed2,rank2,depth2,frontier2,table2,found] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix fields result
  rw [he]
  simp only [impSubst,conjunctionSubst,lengthSubst,notSubst,eqnSubst,graph2,graph3,programSubst,boundedSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rawPredicateInstantiate (n : Nat) (arity : Fin n → Nat) (V : Program 3) {alpha : Type}  (raw : OTerm alpha) :
    instantiate (rawPredicate n arity V) (emb raw) = AtRaw n arity V raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename (n : Nat) (arity : Fin n → Nat) (V : Program 3) {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw n arity V raw).relabel j = BelowRaw n arity V (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl

theorem rawPredicateLift (n : Nat) (arity : Fin n → Nat) (V : Program 3) {alpha : Type}  :
    lift (rawPredicate n arity V (alpha := alpha)) = rawPredicate n arity V (alpha := alpha ⊕ Fin 1) := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.InductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedCacheCoherence.InductionSyntaxProof
