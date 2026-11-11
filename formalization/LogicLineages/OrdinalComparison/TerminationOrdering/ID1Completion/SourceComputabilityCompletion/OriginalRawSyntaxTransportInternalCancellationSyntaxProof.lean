module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationSyntaxProof
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
open OriginalRawSyntaxTransportInternalCancellation
open InternalStrongInduction

theorem atRawSubst {alpha beta : Type} (p q : Program 3)
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw p q raw).subst (fun a => emb (ts a)) = AtRaw p q (raw.subst ts) := by
  unfold AtRaw cancellationMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,graph3,programSubst,numeral,zSubst,
    consTermSubst,emptySubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename {alpha beta : Type} (p q : Program 3)
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw p q raw).relabel j = AtRaw p q (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw p q raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem cancellationMatrixWitness {alpha : Type} (p q : Program 3)
    (raw d k shifted : OTerm alpha) :
    (cancellationMatrix p q raw).subst
      (Sum.elim Term.var (fun i => emb (![d,k,shifted] i))) =
      (graph3 p shifted (numeral 0) k raw).imp (graph3 q raw d k shifted) := by
  have he : (Sum.elim Term.var (fun i => emb (![d,k,shifted] i))) =
      (fun a => emb (Sum.elim Term.var ![d,k,shifted] a)) := by
    funext a
    cases a <;> rfl
  unfold cancellationMatrix
  rw [he]
  simp only [impSubst,graph3,programSubst,numeral,zSubst,
    consTermSubst,emptySubst,witnessLift,Term.subst,Sum.elim_inr]
  all_goals rfl

theorem rawPredicateInstantiate {alpha : Type} (p q : Program 3) (raw : OTerm alpha) :
    instantiate (rawPredicate p q) (emb raw) = AtRaw p q raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename {alpha beta : Type} (p q : Program 3)
    (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw p q raw).relabel j = BelowRaw p q (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl

theorem rawPredicateLift {alpha : Type} (p q : Program 3) :
    lift (rawPredicate p q (alpha := alpha)) = rawPredicate p q (alpha := alpha ⊕ Fin 1) := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationSyntaxProof
