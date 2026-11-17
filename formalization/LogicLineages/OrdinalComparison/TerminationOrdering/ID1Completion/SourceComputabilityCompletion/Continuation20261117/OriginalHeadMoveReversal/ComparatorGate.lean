module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalHeadMoveReversal.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalHeadMoveReversal.ComparatorGate
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115 Continuation20261116
theorem exactOriginalHeadMoveReversal : Targets.InternalReversal ↔
  (∀ (n : Nat) (arity : Fin n → Nat)
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
      ![targetHead,targetBase,sourceHead,sourceBase,symbols,types]))) := Iff.rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalHeadMoveReversal.ComparatorGate
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalHeadMoveReversal.ComparatorGate
