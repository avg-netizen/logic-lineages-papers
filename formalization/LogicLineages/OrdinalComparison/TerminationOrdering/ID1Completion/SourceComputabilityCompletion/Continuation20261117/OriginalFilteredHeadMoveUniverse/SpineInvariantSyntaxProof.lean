module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineInvariantDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.EntryFactsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineInvariantSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SpineInvariant
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst orSubst)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open InternalStrongInduction
open OriginalContextInsertionSyntaxProof (lengthSubst)

open Continuation20261115.OriginalArgumentPermutationClosure.CountAgreementSyntaxProof
attribute [local irreducible] programGraph

open OriginalUniverseDecoderTransportSyntaxProof
open EntryFactsSyntaxProof
theorem domainSubst {alpha beta : Type} (n : Nat) (raw entries : OTerm alpha) (ts : alpha → OTerm beta) :
    (domain n raw entries).subst (fun a => emb (ts a)) =
      domain n (raw.subst ts) (entries.subst ts) := by
  simp only [domain,conjunctionSubst,graph2,sucSubst,zSubst,graph1,programSubst,consTermSubst,emptySubst]
@[simp] theorem domainRename {alpha beta : Type} (n : Nat) (raw entries : OTerm alpha) (j : alpha → beta) :
    (domain n raw entries).relabel j = domain n (raw.relabel j) (entries.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (domain n raw entries).subst (fun a => emb (.var (j a))) = _
  rw [domainSubst]
  simp only [← termRelabelAsSubst]

theorem plainSubst {alpha beta : Type} (H : Program 1) (types raw gamma : OTerm alpha) (ts : alpha → OTerm beta) :
    (Plain H types raw gamma).subst (fun a => emb (ts a)) =
      Plain H (types.subst ts) (raw.subst ts) (gamma.subst ts) := by
  exact OriginalTypedDecoderTransportSyntaxProof.acceptedSubst H true types raw gamma ts
@[simp] theorem plainRename {alpha beta : Type} (H : Program 1) (types raw gamma : OTerm alpha) (j : alpha → beta) :
    (Plain H types raw gamma).relabel j = Plain H (types.relabel j) (raw.relabel j) (gamma.relabel j) := by
  exact OriginalTypedDecoderTransportSyntaxProof.acceptedRename H true types raw gamma j

theorem rowSubst {alpha beta : Type} (n : Nat) (H : Program 1) (M W : Program 2)
    (raw types entries gamma context : OTerm alpha) (ts : alpha → OTerm beta) :
    (row n H M W raw types entries gamma context).subst (fun a => emb (ts a)) =
      row n H M W (raw.subst ts) (types.subst ts) (entries.subst ts) (gamma.subst ts) (context.subst ts) := by
  simp only [SpineInvariant.row,impSubst,conjunctionSubst,domainSubst,allGoodSubst,plainSubst,acceptedSubst]
@[simp] theorem rowRename {alpha beta : Type} (n : Nat) (H : Program 1) (M W : Program 2)
    (raw types entries gamma context : OTerm alpha) (j : alpha → beta) :
    (row n H M W raw types entries gamma context).relabel j =
      row n H M W (raw.relabel j) (types.relabel j) (entries.relabel j) (gamma.relabel j) (context.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row n H M W raw types entries gamma context).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem atRawSubst {alpha beta : Type} (n : Nat) (H : Program 1) (M W : Program 2) (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw n H M W raw).subst (fun a => emb (ts a)) = AtRaw n H M W (raw.subst ts) := by
  unfold AtRaw matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [rowSubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem atRawRename {alpha beta : Type} (n : Nat) (H : Program 1) (M W : Program 2) (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw n H M W raw).relabel j = AtRaw n H M W (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw n H M W raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (n : Nat) (H : Program 1) (M W : Program 2)
    (raw types entries gamma context : OTerm alpha) :
    (matrix n H M W raw).subst (Sum.elim Term.var (fun i => emb (![types,entries,gamma,context] i))) =
      row n H M W raw types entries gamma context := by
  have he : (Sum.elim Term.var (fun i => emb (![types,entries,gamma,context] i))) =
      (fun a => emb (Sum.elim Term.var ![types,entries,gamma,context] a)) := by
    funext a; cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [rowSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem predicateInstantiate {alpha : Type} (n : Nat) (H : Program 1) (M W : Program 2) (raw : OTerm alpha) :
    instantiate (predicate n H M W) (emb raw) = AtRaw n H M W raw := by
  rw [predicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]
@[simp] theorem belowRawRename {alpha beta : Type} (n : Nat) (H : Program 1) (M W : Program 2) (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw n H M W raw).relabel j = BelowRaw n H M W (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold predicate
  rw [atRawRename]
  rfl

theorem predicateLift {alpha : Type} (n : Nat) (H : Program 1) (M W : Program 2) :
    lift (predicate (alpha := alpha) n H M W) = predicate (alpha := alpha ⊕ Fin 1) n H M W := by
  unfold lift predicate
  rw [atRawRename]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineInvariantSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineInvariantSyntaxProof
