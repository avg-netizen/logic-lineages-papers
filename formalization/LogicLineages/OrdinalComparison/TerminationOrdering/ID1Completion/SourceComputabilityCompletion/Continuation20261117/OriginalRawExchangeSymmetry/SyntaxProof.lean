module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.AllSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.SyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Definitions
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalGraphCompositionSyntaxProof InternalRawListRecursionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalTagArithmeticSyntaxProof InternalControlGraphSupportProof
open InternalStrongInduction InternalStrongInductionSyntaxProof
open WindowSourceHeadInclusion.ClosureSyntaxProof (closureSubst closureRename)
open AllSyntaxProof
theorem predicateInstantiate (n : Nat) (arity : Fin n → Nat) (raw : OTerm alpha) :
    instantiate (predicate n arity) (emb raw) = AtRaw n arity raw := by
  rw [predicate,instantiate,bindEmbedding]
  change (allSchema _ _ _).subst (fun a => emb (Sum.elim Term.var (fun _ => raw) a)) = _
  rw [allSubst]
  rfl
@[simp] theorem belowRawRename (n : Nat) (arity : Fin n → Nat) (raw : OTerm alpha) {beta : Type} (j : alpha → beta) :
    (BelowRaw n arity raw).relabel j = BelowRaw n arity (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold predicate
  rw [atRawRename]
  rfl
theorem predicateLift (n : Nat) (arity : Fin n → Nat) :
    lift (predicate (alpha := alpha) n arity) = predicate (alpha := alpha ⊕ Fin 1) n arity := by
  unfold lift predicate
  rw [atRawRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.SyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.SyntaxProof
