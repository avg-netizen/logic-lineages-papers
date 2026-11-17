module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeInductionAtRawSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeInductionSyntaxProof
open Continuation20261114 Continuation20261115 Continuation20261116
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
open ExchangeInduction
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst orSubst)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open InternalStrongInduction
open OriginalContextInsertionSyntaxProof (lengthSubst)

attribute [local irreducible] programGraph

theorem matrixWitness {alpha : Type} (n : Nat) (arity : Fin n → Nat) (source target node window lv rv : OTerm alpha) :
    (matrix n arity source).subst (Sum.elim Term.var (fun i => emb (![target,node,window,lv,rv] i))) =
      (fields n arity source target node window lv rv).imp (eqn lv rv) := by
  exact matrixSchemaWitness OriginalRawSyntaxTransport.variableRankRaw
    (Continuation20261115.OriginalDecodedExchangeEquation.exchange n arity) source target node window lv rv
theorem predicateInstantiate {alpha : Type} (n : Nat) (arity : Fin n → Nat) (raw : OTerm alpha) :
    instantiate (predicate n arity) (emb raw) = AtRaw n arity raw := by
  rw [predicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]

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
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeInductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeInductionSyntaxProof
