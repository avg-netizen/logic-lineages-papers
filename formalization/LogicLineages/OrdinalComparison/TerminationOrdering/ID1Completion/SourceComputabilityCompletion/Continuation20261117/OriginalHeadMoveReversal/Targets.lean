module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalGuardedHeadSourceCoverage.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalHeadMoveReversal.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115 Continuation20261116
/-- Exact original headMove reversal. Source head validity and actual arrow
closure remain explicit. No target validity, reverse window, enumeration,
permutation, symmetry or metadata oracle is assumed. -/
def InternalReversal : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (sourceHead sourceBase targetHead targetBase symbols types : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) sourceHead)) →
  Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types)) →
  Nonempty (Derivation body Delta
    (programGraph (OriginalHeadMove.headMove n arity) (numeral 1)
      ![sourceHead,sourceBase,targetHead,targetBase,symbols,types])) →
  Nonempty (Derivation body Delta
    (programGraph (OriginalHeadMove.headMove n arity) (numeral 1)
      ![targetHead,targetBase,sourceHead,sourceBase,symbols,types]))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalHeadMoveReversal.Targets
