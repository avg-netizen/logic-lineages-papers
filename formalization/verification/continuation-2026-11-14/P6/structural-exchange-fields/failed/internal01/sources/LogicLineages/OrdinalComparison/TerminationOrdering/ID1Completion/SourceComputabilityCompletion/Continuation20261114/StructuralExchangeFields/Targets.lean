module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.Targets
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
/-- Genuine source-shaped branch law: NO field-graph correctness premises.
All intermediate field values are supplied by actual total program graphs. -/
def InternalApplication : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (U : Fin 19 → Program 3) (V : Program 3) (cons : Bool)
    (node code param source target sigma tau q a r b h0 t0 h1 t1 h2 t2 h3 t3 : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph3
    (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor)
    source sigma q a)) →
  Nonempty (Derivation body Delta (graph3
    (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor)
    target tau r b)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code h0 t0)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t0 h1 t1)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t1 h2 t2)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t2 h3 t3)) →
  (Nonempty (Derivation body Delta (graph3 (layer U V) (numeral 2) node code param)) ↔
   Nonempty (Derivation body Delta (eqn sigma tau ⊓
     ((eqn a b ⊓ eqn h0 (numeral 1)) ⊔ (eqn q r ⊓ eqn h3 (numeral 1))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.Targets
