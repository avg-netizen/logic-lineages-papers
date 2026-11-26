module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def NativeFields : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (U : Fin 19 → Program 3) (V : Program 3),
  (∀ i v, evaluate (U i) v = TransparentExchangeLayer.fieldValue n arity i v) →
  (∀ v, evaluate V v = TransparentExchangeLayer.validValue n v) →
  (∀ i v, evaluate (fields U V i) v = TransparentExchangeLayer.fieldValue n arity i v) ∧
  (∀ v, evaluate (layer U V) v = ExchangeNumericSuppliers.layerValue n arity v)
/-- Only genuine unpaid headMove remains a field-output premise. Head encodings
and results are provided by the actual paid converters on the constructor heads. -/
def InternalOrdinary : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (U : Fin 19 → Program 3) (V : Program 3)
    (node code param source target f g base dest ef eg rf rg move h0 t0 : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source f base)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor target g dest)) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead ef f)) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead eg g)) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadResult.headResult rf f)) →
  Nonempty (Derivation body Delta (graph1 OriginalHeadResult.headResult rg g)) →
  Nonempty (Derivation body Delta (graph3 (U 16) move node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code h0 t0)) →
  (Nonempty (Derivation body Delta (graph3 (layer U V) (numeral 2) node code param)) ↔
   Nonempty (Derivation body Delta
     ((eqn move (numeral 1) ⊓ eqn rg rf) ⊔ (eqn ef eg ⊓ eqn h0 (numeral 1)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ResultStructuralFields.Targets
