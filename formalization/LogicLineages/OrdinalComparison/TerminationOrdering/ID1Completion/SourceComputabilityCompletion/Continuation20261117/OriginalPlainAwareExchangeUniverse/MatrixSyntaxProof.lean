module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.InductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.MatrixSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (emb)
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalStrongInduction
open Induction InductionSyntaxProof

theorem atModeSubst {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtMode n arity arguments raw).subst (fun a => emb (ts a)) = AtMode n arity arguments (raw.subst ts) := by
  unfold AtMode matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [rowSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem atRawSubst {alpha beta : Type} (n : Nat) (arity : Fin n → Nat)
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw n arity raw).subst (fun a => emb (ts a)) = AtRaw n arity (raw.subst ts) := by
  simp only [AtRaw,conjunctionSubst,atModeSubst]
@[simp] theorem atRawRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat)
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw n arity raw).relabel j = AtRaw n arity (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw n arity raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {alpha : Type} (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (source typ target gamma context symbols types window node : OTerm alpha) :
    (matrix n arity arguments source).subst
      (Sum.elim Term.var (fun i => emb (![typ,target,gamma,context,symbols,types,window,node] i))) =
      row n arity arguments source typ target gamma context symbols types window node := by
  have he : (Sum.elim Term.var (fun i => emb (![typ,target,gamma,context,symbols,types,window,node] i))) =
      (fun a => emb (Sum.elim Term.var ![typ,target,gamma,context,symbols,types,window,node] a)) := by
    funext a; cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [rowSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem predicateInstantiate {alpha : Type} (n : Nat) (arity : Fin n → Nat) (raw : OTerm alpha) :
    instantiate (predicate n arity) (emb raw) = AtRaw n arity raw := by
  rw [predicate,instantiate,InternalTagArithmeticSyntaxProof.bindEmbedding,atRawSubst]
  simp only [InternalTagArithmeticSyntaxProof.varBind]
@[simp] theorem belowRawRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw n arity raw).relabel j = BelowRaw n arity (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold predicate
  rw [atRawRename]
  rfl
theorem predicateLift {alpha : Type} (n : Nat) (arity : Fin n → Nat) :
    lift (predicate (alpha := alpha) n arity) = predicate (alpha := alpha ⊕ Fin 1) n arity := by
  unfold lift predicate
  rw [atRawRename]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.MatrixSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.MatrixSyntaxProof
