module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
/-- Exact ordinary-head recurrence of the literal standalone decoded AST.
The encoded-equality test is kept intact; no unproved raw-head injectivity or
semantic equality is silently substituted. All head outputs and answers are
internal witnesses. Guard rejection remains false; standalone success is1. -/
def InternalOrdinary : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target f g base dest node child param symbols types : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source f base)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor target g dest)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child base dest)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbols types)) →
  (Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param)) ↔
   Nonempty (Derivation body Delta
     (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param ⊓
       ((programGraph (OriginalHeadMove.headMove n arity) (numeral 1) ![f,base,g,dest,symbols,types] ⊓
          graph2 resultEqual (numeral 1) g f) ⊔
        (graph2 encodedEqual (numeral 1) f g ⊓
          graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) child param)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.Targets
