module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.InductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
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
open Induction
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open InternalStrongInduction

theorem implicationRename {alpha beta : Type} (p q : Formula alpha) (j : alpha → beta) :
    (p.imp q).relabel j = (p.relabel j).imp (q.relabel j) := rfl
theorem notRename {alpha beta : Type} (p : Formula alpha) (j : alpha → beta) :
    p.not.relabel j = (p.relabel j).not := rfl

@[simp] theorem resultRename {alpha beta : Type}
    (raw reached candidate parameter out value : OTerm alpha) (j : alpha → beta) :
    (result raw reached candidate parameter out value).relabel j =
      result (raw.relabel j) (reached.relabel j) (candidate.relabel j) (parameter.relabel j) (out.relabel j) (value.relabel j) := by
  simp only [result,qualifies,implicationRename,notRename,eqnRelabel,conjunctionRename,graph2,graph3,programRename,consTermRename,emptyRename,numeral,sucRelabel,zRelabel]

theorem atRawSubst (H : Program 1) {alpha beta : Type} 
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw H raw).subst (fun a => emb (ts a)) = AtRaw H (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,notSubst,equalSubst,fields,result,qualifies,eqnSubst,graph2,graph3,graph3,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename (H : Program 1) {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw H raw).relabel j = AtRaw H (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw H raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness (H : Program 1) {alpha : Type} (input reached candidate parameter out value : OTerm alpha) :
    (matrix H input).subst (Sum.elim Term.var (fun i => emb (![reached,candidate,parameter,out,value] i))) =
      (fields H input reached candidate parameter out value).imp (result input reached candidate parameter out value) := by
  have he : (Sum.elim Term.var (fun i => emb (![reached,candidate,parameter,out,value] i))) =
      (fun a => emb (Sum.elim Term.var ![reached,candidate,parameter,out,value] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix fields
  rw [he]
  simp only [impSubst,conjunctionSubst,notSubst,result,qualifies,eqnSubst,graph2,graph3,programSubst,numeral,zSubst,sucSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rawPredicateInstantiate (H : Program 1) {alpha : Type}  (raw : OTerm alpha) :
    instantiate (rawPredicate H) (emb raw) = AtRaw H raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename (H : Program 1) {alpha beta : Type} 
    (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw H raw).relabel j = BelowRaw H (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl

theorem rawPredicateLift (H : Program 1) {alpha : Type}  :
    lift (rawPredicate H (alpha := alpha)) = rawPredicate H (alpha := alpha ⊕ Fin 1) := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.InductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.InductionSyntaxProof
