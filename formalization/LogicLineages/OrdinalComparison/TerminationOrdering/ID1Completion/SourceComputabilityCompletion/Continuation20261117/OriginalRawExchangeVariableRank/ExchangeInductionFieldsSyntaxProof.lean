module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
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

theorem graphOneSubst {alpha beta : Type} (P : Program 1) (out x : OTerm alpha) (ts : alpha → OTerm beta) :
    (graph1 P out x).subst (fun a => emb (ts a)) = graph1 P (out.subst ts) (x.subst ts) := by
  simp only [graph1,programSubst,consTermSubst,emptySubst]
theorem graphTwoSubst {alpha beta : Type} (P : Program 2) (out x y : OTerm alpha) (ts : alpha → OTerm beta) :
    (graph2 P out x y).subst (fun a => emb (ts a)) = graph2 P (out.subst ts) (x.subst ts) (y.subst ts) := by
  simp only [graph2,programSubst,consTermSubst,emptySubst]

theorem fieldsSubst {alpha beta : Type} (n : Nat) (arity : Fin n → Nat)
    (source target node window lv rv : OTerm alpha) (ts : alpha → OTerm beta) :
    (fields n arity source target node window lv rv).subst (fun a => emb (ts a)) =
      fields n arity (source.subst ts) (target.subst ts) (node.subst ts) (window.subst ts) (lv.subst ts) (rv.subst ts) := by
  simp only [fields,conjunctionSubst,graphOneSubst,graphTwoSubst,sucSubst,zSubst]
@[simp] theorem fieldsRename {alpha beta : Type} (n : Nat) (arity : Fin n → Nat)
    (source target node window lv rv : OTerm alpha) (j : alpha → beta) :
    (fields n arity source target node window lv rv).relabel j =
      fields n arity (source.relabel j) (target.relabel j) (node.relabel j) (window.relabel j) (lv.relabel j) (rv.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fields n arity source target node window lv rv).subst (fun a => emb (.var (j a))) = _
  rw [fieldsSubst]
  simp only [← termRelabelAsSubst]


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeInductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeInductionSyntaxProof
