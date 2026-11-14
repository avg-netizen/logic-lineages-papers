module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterSyntaxProof
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
open Filter
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open InternalStrongInduction

@[simp] theorem resultRename (E : Program 3) {alpha beta : Type}
    (raw reached candidate parameter : OTerm alpha) (j : alpha → beta) :
    (result E raw reached candidate parameter).relabel j =
      result E (raw.relabel j) (reached.relabel j) (candidate.relabel j) (parameter.relabel j) := by
  simp only [result,conjunctionRename,graph2,graph3,programRename,consTermRename,emptyRename,numeral,sucRelabel,zRelabel]

theorem atRawSubst (E : Program 3) {alpha beta : Type} 
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw E raw).subst (fun a => emb (ts a)) = AtRaw E (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,equalSubst,fields,result,graph2,graph3,graph3,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename (E : Program 3) {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw E raw).relabel j = AtRaw E (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw E raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (E : Program 3) {alpha : Type} (input reached candidate parameter out : OTerm alpha) :
    (matrix E input).subst (Sum.elim Term.var (fun i => emb (![reached,candidate,parameter,out] i))) =
      (fields E input reached candidate parameter out).imp (result E input reached candidate parameter) := by
  have he : (Sum.elim Term.var (fun i => emb (![reached,candidate,parameter,out] i))) =
      (fun a => emb (Sum.elim Term.var ![reached,candidate,parameter,out] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix fields
  rw [he]
  simp only [impSubst,conjunctionSubst,result,graph2,graph3,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rawPredicateInstantiate (E : Program 3) {alpha : Type}  (raw : OTerm alpha) :
    instantiate (rawPredicate E) (emb raw) = AtRaw E raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename (E : Program 3) {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw E raw).relabel j = BelowRaw E (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl

theorem rawPredicateLift (E : Program 3) {alpha : Type}  :
    lift (rawPredicate E (alpha := alpha)) = rawPredicate E (alpha := alpha ⊕ Fin 1) := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterSyntaxProof
