module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261115
/-- Actual successful original raw exchange preserves the COMPLETE original
(size,maxLabel) pair. No source/target typing, image, validity, recursive bounds,
permutation semantic oracle or source coverage premise is supplied. Original
raw decoder and window rejection are internal cases, not erased hypotheses.
This endpoint makes no arbitrary-H source preservation claim. -/
def InternalBoundsPreserved : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (node window left right leftBounds rightBounds : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)) →
  Nonempty (Derivation body Delta
    (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node window)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) leftBounds left)) →
  Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rightBounds right)) →
  Nonempty (Derivation body Delta (eqn leftBounds rightBounds))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.Targets
