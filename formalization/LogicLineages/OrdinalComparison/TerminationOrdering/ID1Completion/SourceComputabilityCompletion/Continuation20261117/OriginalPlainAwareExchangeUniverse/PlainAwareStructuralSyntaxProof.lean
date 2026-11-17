module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralSyntaxProof
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
open PlainAwareStructuralDefinitions
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst orSubst)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open InternalStrongInduction
open OriginalContextInsertionSyntaxProof (lengthSubst)

open OriginalUniverseDecoderTransportSyntaxProof
attribute [local irreducible] programGraph

theorem checkedSubst {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (mode : Bool) (typ raw gamma context : OTerm alpha) (ts : alpha → OTerm beta) :
    (Checked n arity M W mode typ raw gamma context).subst (fun a => emb (ts a)) =
      Checked n arity M W mode (typ.subst ts) (raw.subst ts) (gamma.subst ts) (context.subst ts) := by
  exact acceptedSubst _ M W mode typ raw gamma context ts
@[simp] theorem checkedRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (mode : Bool) (typ raw gamma context : OTerm alpha) (j : alpha → beta) :
    (Checked n arity M W mode typ raw gamma context).relabel j =
      Checked n arity M W mode (typ.relabel j) (raw.relabel j) (gamma.relabel j) (context.relabel j) := by
  exact acceptedRename _ M W mode typ raw gamma context j

theorem plainSubst {alpha beta : Type} (n : Nat) (arity : Fin n → Nat)
 (mode : Bool) (typ raw gamma : OTerm alpha) (ts : alpha → OTerm beta) :
 (Plain n arity mode typ raw gamma).subst (fun a => emb (ts a)) =
 Plain n arity mode (typ.subst ts) (raw.subst ts) (gamma.subst ts) :=
 OriginalTypedDecoderTransportSyntaxProof.acceptedSubst _ mode typ raw gamma ts
@[simp] theorem plainRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat)
 (mode : Bool) (typ raw gamma : OTerm alpha) (j : alpha → beta) :
 (Plain n arity mode typ raw gamma).relabel j =
 Plain n arity mode (typ.relabel j) (raw.relabel j) (gamma.relabel j) :=
 OriginalTypedDecoderTransportSyntaxProof.acceptedRename _ mode typ raw gamma j

theorem transferSubst {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (mode : Bool) (source target context : OTerm alpha) (ts : alpha → OTerm beta) :
    (Transfer n arity M W mode source target context).subst (fun a => emb (ts a)) =
      Transfer n arity M W mode (source.subst ts) (target.subst ts) (context.subst ts) := by
  unfold Transfer TransferMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,checkedSubst,plainSubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem transferRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (mode : Bool) (source target context : OTerm alpha) (j : alpha → beta) :
    (Transfer n arity M W mode source target context).relabel j =
      Transfer n arity M W mode (source.relabel j) (target.relabel j) (context.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Transfer n arity M W mode source target context).subst (fun a => emb (.var (j a))) = _
  rw [transferSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (mode : Bool) (source target typ gamma context : OTerm alpha) :
    (TransferMatrix n arity M W mode source target context).subst
      (Sum.elim Term.var (fun i => emb (![typ,gamma] i))) =
      ((Checked n arity M W mode typ source gamma context) ⊓
       (Plain n arity mode typ target gamma)).imp
        (Checked n arity M W mode typ target gamma context) := by
  have he : (Sum.elim Term.var (fun i => emb (![typ,gamma] i))) =
      (fun a => emb (Sum.elim Term.var ![typ,gamma] a)) := by
    funext a; cases a <;> rfl
  unfold TransferMatrix
  rw [he]
  simp only [impSubst,conjunctionSubst,checkedSubst,plainSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralSyntaxProof
