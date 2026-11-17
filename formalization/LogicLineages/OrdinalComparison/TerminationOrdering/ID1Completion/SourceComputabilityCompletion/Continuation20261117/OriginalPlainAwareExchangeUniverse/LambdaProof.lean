module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ChildTransferProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.LambdaAtChildProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.LambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open Continuation20261115 Continuation20261116
open OriginalRawSyntaxTransport Induction
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InductionSyntaxProof MatrixSyntaxProof
theorem preserved (n : Nat) (arity : Fin n → Nat)
    (left right lm rm lc rc node window context symbols types : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 lambdaConstructor left lm lc)))
    (hrc : Nonempty (Derivation body Delta (graph2 lambdaConstructor right rm rc)))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (PlainAwareStructuralDefinitions.Transfer n arity
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      false left right context)) := by
  apply InternalAcceptanceSupportProof.programCases InternalPairing.pairing ![lc,rc] _
  intro beta j Theta child hj hchild
  have hx : (fun i => (![lc,rc] i).relabel j) = ![lc.relabel j,rc.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hchild
  rw [PlainAwareStructuralSyntaxProof.transferRename]
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have henv' := renameInto henv j Theta hj
  have hedge' := renameInto hedge j Theta hj
  have ih' := renameInto ih j Theta hj
  rw [graph2Rename] at hlc' hrc'
  rw [environmentRename] at henv'
  rw [edgeRename] at hedge'
  rw [belowRawRename] at ih'
  exact LambdaAtChildProof.atChild n arity (left.relabel j) (right.relabel j)
    (lm.relabel j) (rm.relabel j) (lc.relabel j) (rc.relabel j) (node.relabel j) child
    (window.relabel j) (context.relabel j) (symbols.relabel j) (types.relabel j)
    hlc' hrc' henv' hedge' hchild ih'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.LambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.LambdaProof
