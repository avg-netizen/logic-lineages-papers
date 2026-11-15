module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.SyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.InductionSyntaxProof
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
open InductionDefinitions
open SyntaxProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalSubst)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryUncoveredCount.CompareSyntaxProof (boundedSubst)
open InternalStrongInduction
open OriginalContextInsertionSyntaxProof (lengthSubst)

theorem atRawSubst {alpha beta : Type} (n : Nat) (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtRaw n raw).subst (fun a => emb (ts a)) = AtRaw n (raw.subst ts) := by
  simp only [AtRaw,impSubst,conjunctionSubst,graph1,programSubst,membersSubst,
    numeral,zSubst,sucSubst,consTermSubst,emptySubst]
@[simp] theorem atRawRename {alpha beta : Type} (n : Nat) (raw : OTerm alpha) (j : alpha → beta) :
    (AtRaw n raw).relabel j = AtRaw n (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtRaw n raw).subst (fun a => emb (.var (j a))) = _
  rw [atRawSubst]
  simp only [← termRelabelAsSubst]
theorem rawPredicateInstantiate {alpha : Type} (n : Nat) (raw : OTerm alpha) :
    instantiate (rawPredicate n) (emb raw) = AtRaw n raw := by
  rw [rawPredicate,instantiate,bindEmbedding,atRawSubst]
  simp only [varBind]
@[simp] theorem belowRawRename {alpha beta : Type} (n : Nat) (raw : OTerm alpha) (j : alpha → beta) :
    (BelowRaw n raw).relabel j = BelowRaw n (raw.relabel j) := by
  unfold BelowRaw
  rw [InternalStrongInductionSyntaxProof.belowRename]
  unfold rawPredicate
  rw [atRawRename]
  rfl
theorem rawPredicateLift {alpha : Type} (n : Nat) :
    lift (rawPredicate (alpha := alpha) n) = rawPredicate (alpha := alpha ⊕ Fin 1) n := by
  unfold lift rawPredicate
  rw [atRawRename]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.InductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.InductionSyntaxProof
