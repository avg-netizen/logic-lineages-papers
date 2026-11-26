module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof
open OriginalContextInsertionSyntaxProof (insertSubst insertRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedDecoderTransport
open InternalStrongInduction

theorem acceptedSubst {alpha beta : Type} (H : Program 1) (arguments : Bool)
    (typ raw gamma : OTerm alpha) (ts : alpha → OTerm beta) :
    (Accepted H arguments typ raw gamma).subst (fun a => emb (ts a)) =
      Accepted H arguments (typ.subst ts) (raw.subst ts) (gamma.subst ts) := by
  simp only [Accepted,graph3,programSubst,numeral,sucSubst,zSubst,consTermSubst,emptySubst]

@[simp] theorem acceptedRename {alpha beta : Type} (H : Program 1) (arguments : Bool)
    (typ raw gamma : OTerm alpha) (j : alpha → beta) :
    (Accepted H arguments typ raw gamma).relabel j =
      Accepted H arguments (typ.relabel j) (raw.relabel j) (gamma.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Accepted H arguments typ raw gamma).subst (fun a => emb (.var (j a))) = _
  rw [acceptedSubst]
  simp only [← termRelabelAsSubst]

theorem transportSubst {alpha beta : Type} (H : Program 1) (erasing arguments : Bool)
    (d cutoff gamma extended typ raw transformed : OTerm alpha) (ts : alpha → OTerm beta) :
    (Transport H erasing arguments d cutoff gamma extended typ raw transformed).subst
      (fun a => emb (ts a)) =
      Transport H erasing arguments (d.subst ts) (cutoff.subst ts) (gamma.subst ts)
        (extended.subst ts) (typ.subst ts) (raw.subst ts) (transformed.subst ts) := by
  unfold Transport
  cases erasing <;> simp only [sourceContext,targetContext,Bool.false_eq_true,if_false,if_true,
    impSubst,conjunctionSubst,insertSubst,acceptedSubst,graph3,programSubst,consTermSubst,emptySubst]

@[simp] theorem transportRename {alpha beta : Type} (H : Program 1) (erasing arguments : Bool)
    (d cutoff gamma extended typ raw transformed : OTerm alpha) (j : alpha → beta) :
    (Transport H erasing arguments d cutoff gamma extended typ raw transformed).relabel j =
      Transport H erasing arguments (d.relabel j) (cutoff.relabel j) (gamma.relabel j)
        (extended.relabel j) (typ.relabel j) (raw.relabel j) (transformed.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Transport H erasing arguments d cutoff gamma extended typ raw transformed).subst
    (fun a => emb (.var (j a))) = _
  rw [transportSubst]
  simp only [← termRelabelAsSubst]

theorem atRawSubst {alpha beta : Type} (H : Program 1) (erasing : Bool)
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw H erasing raw).subst (fun a => emb (ts a)) = AtRaw H erasing (raw.subst ts) := by
  unfold AtRaw transportMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [conjunctionSubst,transportSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename {alpha beta : Type} (H : Program 1) (erasing : Bool)
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw H erasing raw).relabel j = AtRaw H erasing (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw H erasing raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem transportMatrixWitness {alpha : Type} (H : Program 1) (erasing : Bool)
    (raw d cutoff gamma extended typ transformed : OTerm alpha) :
    (transportMatrix H erasing raw).subst
      (Sum.elim Term.var (fun i => emb (![d,cutoff,gamma,extended,typ,transformed] i))) =
      Transport H erasing false d cutoff gamma extended typ raw transformed ⊓
        Transport H erasing true d cutoff gamma extended typ raw transformed := by
  have he : (Sum.elim Term.var (fun i => emb (![d,cutoff,gamma,extended,typ,transformed] i))) =
      (fun a => emb (Sum.elim Term.var ![d,cutoff,gamma,extended,typ,transformed] a)) := by
    funext a
    cases a <;> rfl
  unfold transportMatrix
  rw [he]
  simp only [conjunctionSubst,transportSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rawPredicateInstantiate {alpha : Type} (H : Program 1) (erasing : Bool) (raw : OTerm alpha) :
    instantiate (rawPredicate H erasing) (emb raw) = AtRaw H erasing raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename {alpha beta : Type} (H : Program 1) (erasing : Bool)
    (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw H erasing raw).relabel j = BelowRaw H erasing (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl

theorem rawPredicateLift {alpha : Type} (H : Program 1) (erasing : Bool) :
    lift (rawPredicate H erasing (alpha := alpha)) =
      rawPredicate H erasing (alpha := alpha ⊕ Fin 1) := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportSyntaxProof
