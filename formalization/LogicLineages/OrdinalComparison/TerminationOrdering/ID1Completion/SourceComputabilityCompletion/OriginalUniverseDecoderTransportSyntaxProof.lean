module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportSyntaxProof
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
open OriginalUniverseDecoderTransport
open OriginalTypedDecoderTransport (selectedMode sourceContext targetContext)
open InternalStrongInduction

theorem acceptedSubst {alpha beta : Type} (H : Program 1) (M W : Program 2) (arguments : Bool)
    (typ raw gamma c : OTerm alpha) (ts : alpha → OTerm beta) :
    (Accepted H M W arguments typ raw gamma c).subst (fun a => emb (ts a)) =
      Accepted H M W arguments (typ.subst ts) (raw.subst ts) (gamma.subst ts) (c.subst ts) := by
  simp only [Accepted,programSubst,numeral,sucSubst,zSubst,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.quadrupleSubst]

@[simp] theorem acceptedRename {alpha beta : Type} (H : Program 1) (M W : Program 2) (arguments : Bool)
    (typ raw gamma c : OTerm alpha) (j : alpha → beta) :
    (Accepted H M W arguments typ raw gamma c).relabel j =
      Accepted H M W arguments (typ.relabel j) (raw.relabel j) (gamma.relabel j) (c.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Accepted H M W arguments typ raw gamma c).subst (fun a => emb (.var (j a))) = _
  rw [acceptedSubst]
  simp only [← termRelabelAsSubst]

theorem transportSubst {alpha beta : Type} (H : Program 1) (M W : Program 2) (erasing arguments : Bool)
    (d cutoff gamma extended typ raw transformed c : OTerm alpha) (ts : alpha → OTerm beta) :
    (Transport H M W erasing arguments d cutoff gamma extended typ raw transformed c).subst
      (fun a => emb (ts a)) =
      Transport H M W erasing arguments (d.subst ts) (cutoff.subst ts) (gamma.subst ts)
        (extended.subst ts) (typ.subst ts) (raw.subst ts) (transformed.subst ts) (c.subst ts) := by
  unfold Transport
  cases erasing <;> simp only [sourceContext,targetContext,Bool.false_eq_true,if_false,if_true,
    impSubst,conjunctionSubst,insertSubst,acceptedSubst,graph3,programSubst,consTermSubst,emptySubst]

@[simp] theorem transportRename {alpha beta : Type} (H : Program 1) (M W : Program 2) (erasing arguments : Bool)
    (d cutoff gamma extended typ raw transformed c : OTerm alpha) (j : alpha → beta) :
    (Transport H M W erasing arguments d cutoff gamma extended typ raw transformed c).relabel j =
      Transport H M W erasing arguments (d.relabel j) (cutoff.relabel j) (gamma.relabel j)
        (extended.relabel j) (typ.relabel j) (raw.relabel j) (transformed.relabel j) (c.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Transport H M W erasing arguments d cutoff gamma extended typ raw transformed c).subst
    (fun a => emb (.var (j a))) = _
  rw [transportSubst]
  simp only [← termRelabelAsSubst]

theorem atRawSubst {alpha beta : Type} (H : Program 1) (M W : Program 2) (erasing : Bool)
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw H M W erasing raw).subst (fun a => emb (ts a)) = AtRaw H M W erasing (raw.subst ts) := by
  unfold AtRaw transportMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [conjunctionSubst,transportSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename {alpha beta : Type} (H : Program 1) (M W : Program 2) (erasing : Bool)
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw H M W erasing raw).relabel j = AtRaw H M W erasing (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw H M W erasing raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem transportMatrixWitness {alpha : Type} (H : Program 1) (M W : Program 2) (erasing : Bool)
    (raw d cutoff gamma extended typ transformed c : OTerm alpha) :
    (transportMatrix H M W erasing raw).subst
      (Sum.elim Term.var (fun i => emb (![d,cutoff,gamma,extended,typ,transformed,c] i))) =
      Transport H M W erasing false d cutoff gamma extended typ raw transformed c ⊓
        Transport H M W erasing true d cutoff gamma extended typ raw transformed c := by
  have he : (Sum.elim Term.var (fun i => emb (![d,cutoff,gamma,extended,typ,transformed,c] i))) =
      (fun a => emb (Sum.elim Term.var ![d,cutoff,gamma,extended,typ,transformed,c] a)) := by
    funext a
    cases a <;> rfl
  unfold transportMatrix
  rw [he]
  simp only [conjunctionSubst,transportSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rawPredicateInstantiate {alpha : Type} (H : Program 1) (M W : Program 2) (erasing : Bool) (raw : OTerm alpha) :
    instantiate (rawPredicate H M W erasing) (emb raw) = AtRaw H M W erasing raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename {alpha beta : Type} (H : Program 1) (M W : Program 2) (erasing : Bool)
    (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw H M W erasing raw).relabel j = BelowRaw H M W erasing (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl

theorem rawPredicateLift {alpha : Type} (H : Program 1) (M W : Program 2) (erasing : Bool) :
    lift (rawPredicate H M W erasing (alpha := alpha)) =
      rawPredicate H M W erasing (alpha := alpha ⊕ Fin 1) := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportSyntaxProof
