module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalSyntaxProof
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
open OriginalTwoDeletionInternalDefinitions
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open InternalStrongInduction

theorem atRawSubst {alpha beta : Type} (p : Program 3)
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw p raw).subst (fun a => emb (ts a)) = AtRaw p (raw.subst ts) := by
  unfold AtRaw commutationMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,equalSubst,fields,InternalLessThan.strictLess,orderSubst,sucSubst,graph3,programSubst,numeral,zSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename {alpha beta : Type} (p : Program 3)
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw p raw).relabel j = AtRaw p (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw p raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem commutationMatrixWitness {alpha : Type} (p : Program 3)
    (raw a b i j upper lower left right : OTerm alpha) :
    (commutationMatrix p raw).subst
      (Sum.elim Term.var (fun k => emb (![a,b,i,j,upper,lower,left,right] k))) =
      (fields p raw a b i j upper lower left right).imp (equal left right) := by
  have he : (Sum.elim Term.var (fun k => emb (![a,b,i,j,upper,lower,left,right] k))) =
      (fun x => emb (Sum.elim Term.var ![a,b,i,j,upper,lower,left,right] x)) := by
    funext x
    cases x <;> rfl
  unfold commutationMatrix fields
  rw [he]
  simp only [impSubst,conjunctionSubst,equalSubst,InternalLessThan.strictLess,orderSubst,sucSubst,
    graph3,programSubst,consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  all_goals rfl

theorem rawPredicateInstantiate {alpha : Type} (p : Program 3) (raw : OTerm alpha) :
    instantiate (rawPredicate p) (emb raw) = AtRaw p raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename {alpha beta : Type} (p : Program 3)
    (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw p raw).relabel j = BelowRaw p (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl

theorem rawPredicateLift {alpha : Type} (p : Program 3) :
    lift (rawPredicate p (alpha := alpha)) = rawPredicate p (alpha := alpha ⊕ Fin 1) := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalSyntaxProof
