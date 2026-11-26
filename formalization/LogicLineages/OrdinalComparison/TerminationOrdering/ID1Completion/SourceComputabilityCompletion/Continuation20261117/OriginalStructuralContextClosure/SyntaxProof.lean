module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.SyntaxProof
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
open Definitions
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

theorem transferSubst {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (mode : Bool) (source target : OTerm alpha) (ts : alpha → OTerm beta) :
    (Transfer n arity M W mode source target).subst (fun a => emb (ts a)) =
      Transfer n arity M W mode (source.subst ts) (target.subst ts) := by
  unfold Transfer TransferMatrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,checkedSubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem transferRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (mode : Bool) (source target : OTerm alpha) (j : alpha → beta) :
    (Transfer n arity M W mode source target).relabel j =
      Transfer n arity M W mode (source.relabel j) (target.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (Transfer n arity M W mode source target).subst (fun a => emb (.var (j a))) = _
  rw [transferSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (mode : Bool) (source target typ gamma context : OTerm alpha) :
    (TransferMatrix n arity M W mode source target).subst
      (Sum.elim Term.var (fun i => emb (![typ,gamma,context] i))) =
      (Checked n arity M W mode typ source gamma context).imp
        (Checked n arity M W mode typ target gamma context) := by
  have he : (Sum.elim Term.var (fun i => emb (![typ,gamma,context] i))) =
      (fun a => emb (Sum.elim Term.var ![typ,gamma,context] a)) := by
    funext a; cases a <;> rfl
  unfold TransferMatrix
  rw [he]
  simp only [impSubst,checkedSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.SyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.SyntaxProof
