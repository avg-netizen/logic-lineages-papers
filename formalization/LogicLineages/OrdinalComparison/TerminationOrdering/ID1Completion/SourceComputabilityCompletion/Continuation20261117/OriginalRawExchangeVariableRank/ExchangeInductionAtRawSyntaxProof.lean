module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeInductionGenericSyntaxProof
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
open Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open InternalStrongInduction
open OriginalContextInsertionSyntaxProof (lengthSubst)

attribute [local irreducible] programGraph

theorem atRawSubst {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw n arity raw).subst (fun a => emb (ts a)) = AtRaw n arity (raw.subst ts) := by
  exact allSchemaSubst OriginalRawSyntaxTransport.variableRankRaw
    (Continuation20261115.OriginalDecodedExchangeEquation.exchange n arity) raw ts
@[simp] theorem atRawRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat) (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw n arity raw).relabel j = AtRaw n arity (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw n arity raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeInductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeInductionSyntaxProof
