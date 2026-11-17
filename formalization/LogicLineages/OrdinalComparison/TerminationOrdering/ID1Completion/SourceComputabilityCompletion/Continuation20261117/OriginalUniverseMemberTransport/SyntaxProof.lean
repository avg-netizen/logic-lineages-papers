module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.InductionDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.SyntaxProof
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
open OriginalUniverseDecoderTransport (Accepted)
open OriginalUniverseDecoderTransportSyntaxProof (acceptedSubst acceptedRename)
open InternalStrongInduction
open Definitions InductionDefinitions

theorem memberIncludedSubst {alpha beta : Type} (M N : Program 2) (c : OTerm alpha) (ts : alpha → OTerm beta) :
    (MemberIncluded M N c).subst (fun a => emb (ts a)) = MemberIncluded M N (c.subst ts) := by
  unfold MemberIncluded
  rw [actualUniversalSubstitution,liftedEmbedding]
  simp only [impSubst,graph2,programSubst,consTermSubst,emptySubst,numeral,zSubst,sucSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem memberIncludedRename {alpha beta : Type} (M N : Program 2) (c : OTerm alpha) (j : alpha → beta) :
    (MemberIncluded M N c).relabel j = MemberIncluded M N (c.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (MemberIncluded M N c).subst (fun a => emb (.var (j a))) = _
  rw [memberIncludedSubst]
  simp only [← termRelabelAsSubst]
theorem memberWitness {alpha : Type} (M N : Program 2) (c typ : OTerm alpha) :
    instantiate ((graph2 M (numeral 1) (.var (.inr 0)) (c.relabel Sum.inl)).imp
      (graph2 N (numeral 1) (.var (.inr 0)) (c.relabel Sum.inl))) (emb typ) =
    (graph2 M (numeral 1) typ c).imp (graph2 N (numeral 1) typ c) := by
  rw [instantiate,bindEmbedding]
  simp only [impSubst,graph2,programSubst,consTermSubst,emptySubst,numeral,zSubst,sucSubst,varBind,liftBind]
theorem transportSubst {alpha beta : Type} (H : Program 1) (M N W : Program 2) (arguments : Bool)
    (typ raw gamma c : OTerm alpha) (ts : alpha → OTerm beta) :
    (Transport H M N W arguments typ raw gamma c).subst (fun a => emb (ts a)) =
      Transport H M N W arguments (typ.subst ts) (raw.subst ts) (gamma.subst ts) (c.subst ts) := by
  simp only [Transport,impSubst,memberIncludedSubst,acceptedSubst]
@[simp] theorem transportRename {alpha beta : Type} (H : Program 1) (M N W : Program 2) (arguments : Bool)
    (typ raw gamma c : OTerm alpha) (j : alpha → beta) :
    (Transport H M N W arguments typ raw gamma c).relabel j =
      Transport H M N W arguments (typ.relabel j) (raw.relabel j) (gamma.relabel j) (c.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Transport H M N W arguments typ raw gamma c).subst (fun a => emb (.var (j a))) = _
  rw [transportSubst]
  simp only [← termRelabelAsSubst]
theorem atRawSubst {alpha beta : Type} (H : Program 1) (M N W : Program 2)
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw H M N W raw).subst (fun a => emb (ts a)) = AtRaw H M N W (raw.subst ts) := by
  unfold AtRaw transportMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [conjunctionSubst,transportSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem atRawRename {alpha beta : Type} (H : Program 1) (M N W : Program 2)
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw H M N W raw).relabel j = AtRaw H M N W (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw H M N W raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem transportMatrixWitness {alpha : Type} (H : Program 1) (M N W : Program 2)
    (raw typ gamma c : OTerm alpha) :
    (transportMatrix H M N W raw).subst
      (Sum.elim Term.var (fun i => emb (![typ,gamma,c] i))) =
      Transport H M N W false typ raw gamma c ⊓
        Transport H M N W true typ raw gamma c := by
  have he : (Sum.elim Term.var (fun i => emb (![typ,gamma,c] i))) =
      (fun a => emb (Sum.elim Term.var ![typ,gamma,c] a)) := by
    funext a
    cases a <;> rfl
  unfold transportMatrix
  rw [he]
  simp only [conjunctionSubst,transportSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rawPredicateInstantiate {alpha : Type} (H : Program 1) (M N W : Program 2) (raw : OTerm alpha) :
    instantiate (rawPredicate H M N W) (emb raw) = AtRaw H M N W raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

@[simp] theorem belowRawRename {alpha beta : Type} (H : Program 1) (M N W : Program 2)
    (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw H M N W raw).relabel j = BelowRaw H M N W (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl

theorem rawPredicateLift {alpha : Type} (H : Program 1) (M N W : Program 2) :
    lift (rawPredicate H M N W (alpha := alpha)) =
      rawPredicate H M N W (alpha := alpha ⊕ Fin 1) := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.SyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.SyntaxProof
