module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.LambdaAtChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.HeadLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.EqualityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.OrdinaryAtChildProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.OrdinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Continuation20261114 Continuation20261115 Continuation20261116
open OriginalRawSyntaxTransport Induction
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InductionSyntaxProof MatrixSyntaxProof
theorem atValues (n : Nat) (arity : Fin n → Nat)
    (left right f g base target node window typ gamma context symbols types : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor left f base)))
    (hrc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor right g target)))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (ha : Nonempty (Derivation body Delta (accepted n arity false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (accepted n arity false typ right gamma context)) := by
  apply InternalAcceptanceSupportProof.programCases InternalPairing.pairing ![base,target] _
  intro beta j Theta child hj hchild
  have hx : (fun i => (![base,target] i).relabel j) = ![base.relabel j,target.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hchild
  rw [acceptedRename]
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  have henv' := renameInto henv j Theta hj
  have hedge' := renameInto hedge j Theta hj
  have ih' := renameInto ih j Theta hj
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  rw [graph2Rename] at hlc' hrc'
  rw [environmentRename] at henv'
  rw [edgeRename] at hedge'
  rw [belowRawRename] at ih'
  rw [acceptedRename] at ha'
  rw [plainRename] at hp'
  exact OrdinaryAtChildProof.atChild n arity (left.relabel j) (right.relabel j)
    (f.relabel j) (g.relabel j) (base.relabel j) (target.relabel j) (node.relabel j) child
    (window.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) (symbols.relabel j) (types.relabel j)
    hlc' hrc' henv' hedge' hchild ih' ha' hp'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.OrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.OrdinaryProof
