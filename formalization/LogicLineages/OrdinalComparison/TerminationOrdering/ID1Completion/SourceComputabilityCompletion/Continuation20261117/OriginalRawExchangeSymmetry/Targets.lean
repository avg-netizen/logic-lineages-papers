module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalHeadMoveReversal.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115
/-- Exact original raw exchange reversal. Both original Code guards and
same-window ArrowClosed remain explicit. No target typing/universe,
reverse guard/dependency/answer-list or external induction supplier. -/
def InternalSymmetry : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target node reverseNode window symbols types : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing reverseNode target source)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing window symbols types)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) source)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) target)) →
  Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types)) →
  Nonempty (Derivation body Delta
    (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node window)) →
  Nonempty (Derivation body Delta
    (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) reverseNode window))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.Targets
