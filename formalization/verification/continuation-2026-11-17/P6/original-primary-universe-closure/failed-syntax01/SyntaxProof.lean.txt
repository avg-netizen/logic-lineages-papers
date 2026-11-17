module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.SyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem acceptedSubst {alpha beta : Type} (n : Nat) (arity : Fin n → Nat)
    (typ raw gamma context : OTerm alpha) (ts : alpha → OTerm beta) :
    (accepted n arity typ raw gamma context).subst (fun a => emb (ts a)) =
      accepted n arity (typ.subst ts) (raw.subst ts) (gamma.subst ts) (context.subst ts) := by
  exact OriginalUniverseDecoderTransportSyntaxProof.acceptedSubst _ _ _ false typ raw gamma context ts

@[simp] theorem acceptedRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat)
    (typ raw gamma context : OTerm alpha) (j : alpha → beta) :
    (accepted n arity typ raw gamma context).relabel j =
      accepted n arity (typ.relabel j) (raw.relabel j) (gamma.relabel j) (context.relabel j) := by
  exact OriginalUniverseDecoderTransportSyntaxProof.acceptedRename _ _ _ false typ raw gamma context j

theorem memberAcceptedSubst {alpha beta : Type} (n : Nat) (arity : Fin n → Nat)
    (reached candidate typ raw gamma context : OTerm alpha) (ts : alpha → OTerm beta) :
    (memberAccepted n arity reached candidate typ raw gamma context).subst (fun a => emb (ts a)) =
      memberAccepted n arity (reached.subst ts) (candidate.subst ts) (typ.subst ts)
        (raw.subst ts) (gamma.subst ts) (context.subst ts) := by
  unfold memberAccepted
  simp only [impSubst,conjunctionSubst,acceptedSubst,graph2,programSubst,
    numeral,zSubst,sucSubst,consTermSubst,emptySubst]

@[simp] theorem memberAcceptedRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat)
    (reached candidate typ raw gamma context : OTerm alpha) (j : alpha → beta) :
    (memberAccepted n arity reached candidate typ raw gamma context).relabel j =
      memberAccepted n arity (reached.relabel j) (candidate.relabel j) (typ.relabel j)
        (raw.relabel j) (gamma.relabel j) (context.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (memberAccepted n arity reached candidate typ raw gamma context).subst
    (fun a => emb (.var (j a))) = _
  rw [memberAcceptedSubst]
  simp only [← termRelabelAsSubst]

theorem allAcceptedSubst {alpha beta : Type} (n : Nat) (arity : Fin n → Nat)
    (reached gamma context : OTerm alpha) (ts : alpha → OTerm beta) :
    (allAccepted n arity reached gamma context).subst (fun a => emb (ts a)) =
      allAccepted n arity (reached.subst ts) (gamma.subst ts) (context.subst ts) := by
  unfold allAccepted
  rw [allBlockSubst,liftedEmbedding]
  simp only [memberAcceptedSubst,liftSubst,Term.subst,Sum.elim_inr]

@[simp] theorem allAcceptedRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat)
    (reached gamma context : OTerm alpha) (j : alpha → beta) :
    (allAccepted n arity reached gamma context).relabel j =
      allAccepted n arity (reached.relabel j) (gamma.relabel j) (context.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (allAccepted n arity reached gamma context).subst (fun a => emb (.var (j a))) = _
  rw [allAcceptedSubst]
  simp only [← termRelabelAsSubst]

theorem memberWitness {alpha : Type} (n : Nat) (arity : Fin n → Nat)
    (reached candidate typ raw gamma context : OTerm alpha) :
    (memberAccepted n arity (reached.relabel Sum.inl)
      (.var (.inr (0 : Fin 3))) (.var (.inr (1 : Fin 3))) (.var (.inr (2 : Fin 3)))
      (gamma.relabel Sum.inl) (context.relabel Sum.inl)).subst
      (Sum.elim Term.var (fun i => emb (![candidate,typ,raw] i))) =
      memberAccepted n arity reached candidate typ raw gamma context := by
  have he : (Sum.elim Term.var (fun i => emb (![candidate,typ,raw] i))) =
      (fun a => emb (Sum.elim Term.var ![candidate,typ,raw] a)) := by
    funext a
    cases a <;> rfl
  rw [he]
  simp only [memberAcceptedSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.SyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.SyntaxProof
