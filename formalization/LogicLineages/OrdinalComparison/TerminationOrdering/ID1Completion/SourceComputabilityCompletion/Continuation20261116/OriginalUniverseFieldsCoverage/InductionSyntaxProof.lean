module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ResultSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (emb)
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalGraphCompositionSyntaxProof InternalRecursionClosureSyntaxProof
open InternalRecursionGraphSyntaxProof InternalRawListRecursionSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalStrongInductionSyntaxProof
open Induction ScalarSyntaxProof ResultSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {alpha : Type}
attribute [local irreducible] programGraph

theorem atModeSubst {beta : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtMode n arity H arguments raw).subst (fun a => emb (ts a)) = AtMode n arity H arguments (raw.subst ts) := by
  unfold AtMode matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [InternalAdditionLawsProof.impSubst,observationsSubst,resultSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem atRawSubst {beta : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1) (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw n arity H raw).subst (fun a => emb (ts a)) = AtRaw n arity H (raw.subst ts) := by
  simp only [AtRaw,conjunctionSubst,atModeSubst]

theorem atModeRename {beta : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool)
    (raw : OTerm alpha) (j : alpha → beta) :
    (AtMode n arity H arguments raw).relabel j = AtMode n arity H arguments (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtMode n arity H arguments raw).subst (fun a => emb (.var (j a))) = _
  rw [atModeSubst]
  simp only [← termRelabelAsSubst]

theorem atRawRename {beta : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1) (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw n arity H raw).relabel j = AtRaw n arity H (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw n arity H raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]

theorem predicateInstantiate (n : Nat) (arity : Fin n → Nat) (H : Program 1) (raw : OTerm alpha) :
    instantiate (predicate n arity H : Formula (alpha ⊕ Fin 1)) (emb raw) = AtRaw n arity H raw := by
  rw [predicate,instantiate,InternalTagArithmeticSyntaxProof.bindEmbedding,atRawSubst]
  simp only [InternalTagArithmeticSyntaxProof.varBind]

theorem predicateLift (n : Nat) (arity : Fin n → Nat) (H : Program 1) :
    InternalStrongInduction.lift (predicate n arity H : Formula (alpha ⊕ Fin 1)) = predicate n arity H := by
  unfold predicate InternalStrongInduction.lift
  rw [atRawRename]
  rfl

attribute [local irreducible] AtRaw

theorem belowRawRename {beta : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1) (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw n arity H raw).relabel j = BelowRaw n arity H (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  congr 1
  unfold predicate
  rw [atRawRename]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionSyntaxProof
