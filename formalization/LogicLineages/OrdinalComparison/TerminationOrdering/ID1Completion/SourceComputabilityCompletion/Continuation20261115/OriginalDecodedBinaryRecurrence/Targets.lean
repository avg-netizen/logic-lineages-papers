module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn z)
open SourceComputabilityFormulaSupportProof (numeral)
/-- Exact original app/argumentsCons clauses. Full row-major dependency and answer
lists contain all four entries, including middle entries and duplicates; only
first/last recursive answers enter the original unchanged-sibling alternatives.
No guard, answer-list, Some, or recursive-equivalence premise is supplied. -/
def InternalBinary : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (cons : Bool)
    (source target sigma tau q a r b node first last param : OTerm alpha),
  Nonempty (Derivation body Delta (graph3
    (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor)
    source sigma q a)) →
  Nonempty (Derivation body Delta (graph3
    (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor)
    target tau r b)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first q r)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last a b)) →
  (Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param)) ↔
   Nonempty (Derivation body Delta
     (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param ⊓
       (eqn sigma tau ⊓
         ((eqn a b ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) first param) ⊔
          (eqn q r ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) last param))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.Targets
