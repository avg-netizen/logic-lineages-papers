module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn z)
open SourceComputabilityFormulaSupportProof (numeral)
/-- Literal original lambda success equation for the concrete standalone AST.
The actual guard is evaluated at dummy answer-code zero because its AST ignores
that slot. Guard success is in the conclusion, not an assumed validity premise.
Standalone success is 1, whereas its underlying optional layer returns Some1=2. -/
def InternalLambda : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target sigma tau q r node child param : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor source sigma q)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor target tau r)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child q r)) →
  (Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param)) ↔
   Nonempty (Derivation body Delta
     (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param ⊓
       (eqn sigma tau ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) child param))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.Targets
