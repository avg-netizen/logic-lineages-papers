module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.InductionSyntaxProof
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
open InternalStrongInduction

theorem atRawSubst (n : Nat) {alpha beta : Type} 
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw n raw).subst (fun a => emb (ts a)) = AtRaw n (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,equalSubst,fields,result,InternalLessThan.strictLess,orderSubst,graph2,graph3,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename (n : Nat) {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw n raw).relabel j = AtRaw n (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw n raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (n : Nat) {alpha : Type} (raw fuel1 bound1 table1 fuel2 bound2 table2 : OTerm alpha) :
    (matrix n raw).subst (Sum.elim Term.var (fun i => emb (![fuel1,bound1,table1,fuel2,bound2,table2] i))) =
      (fields n raw fuel1 bound1 table1 fuel2 bound2 table2).imp (result n raw fuel1 bound1 table1 fuel2 bound2 table2) := by
  have he : (Sum.elim Term.var (fun i => emb (![fuel1,bound1,table1,fuel2,bound2,table2] i))) =
      (fun a => emb (Sum.elim Term.var ![fuel1,bound1,table1,fuel2,bound2,table2] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix fields result
  rw [he]
  simp only [impSubst,conjunctionSubst,InternalLessThan.strictLess,orderSubst,graph2,graph3,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rawPredicateInstantiate (n : Nat) {alpha : Type}  (raw : OTerm alpha) :
    instantiate (rawPredicate n) (emb raw) = AtRaw n raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename (n : Nat) {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw n raw).relabel j = BelowRaw n (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl

theorem rawPredicateLift (n : Nat) {alpha : Type}  :
    lift (rawPredicate (alpha := alpha) n) = rawPredicate (alpha := alpha ⊕ Fin 1) n := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.InductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.InductionSyntaxProof
