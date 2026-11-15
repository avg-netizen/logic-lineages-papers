module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryInductionSyntaxProof
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
open EntryInductionDefinitions
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open InternalStrongInduction
open OriginalTypedDecoderInternalAcceptanceSyntaxProof
open OriginalContextInsertionSyntaxProof (lengthSubst)
variable (H : Program 1)

theorem atRawSubst {alpha beta : Type} 
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw H raw).subst (fun a => emb (ts a)) = AtRaw H (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,equalSubst,fields,result,argumentsAcceptedSubst,termAcceptedSubst,lengthSubst,notSubst,eqnSubst,graph2,graph3,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw H raw).relabel j = AtRaw H (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw H raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst H]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (raw types gamma param entries entry tau child : OTerm alpha) :
    (matrix H raw).subst (Sum.elim Term.var (fun i => emb (![types,gamma,param,entries,entry,tau,child] i))) =
      (fields H raw types gamma param entries entry tau child).imp (result H raw types gamma param entries entry tau child) := by
  have he : (Sum.elim Term.var (fun i => emb (![types,gamma,param,entries,entry,tau,child] i))) =
      (fun a => emb (Sum.elim Term.var ![types,gamma,param,entries,entry,tau,child] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix fields result
  rw [he]
  simp only [impSubst,conjunctionSubst,argumentsAcceptedSubst,termAcceptedSubst,lengthSubst,notSubst,eqnSubst,graph2,graph3,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rawPredicateInstantiate {alpha : Type}  (raw : OTerm alpha) :
    instantiate (rawPredicate H) (emb raw) = AtRaw H raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst H]
  simp only [varBind]

@[simp] theorem belowRawRename {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw H raw).relabel j = BelowRaw H (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongEntryInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename H]
  rfl

theorem rawPredicateLift {alpha : Type}  :
    lift (rawPredicate (alpha := alpha) H) = rawPredicate (alpha := alpha ⊕ Fin 1) H := by
  unfold lift rawPredicate
  rw [atRawRename H]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryInductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.TypedArgumentEntriesContent.EntryInductionSyntaxProof
