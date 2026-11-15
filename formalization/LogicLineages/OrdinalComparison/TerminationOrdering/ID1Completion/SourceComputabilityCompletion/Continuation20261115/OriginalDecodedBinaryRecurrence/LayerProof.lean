module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.LayerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
theorem application (n : Nat) (arity : Fin n → Nat) : ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (cons : Bool)
    (node code param source target sigma tau q a r b h0 t0 h1 t1 h2 t2 h3 t3 : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node code param)) →
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
  (Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.layer n arity) (numeral 2) node code param)) ↔
   Nonempty (Derivation body Delta (eqn sigma tau ⊓
     ((eqn a b ⊓ eqn h0 (numeral 1)) ⊔ (eqn q r ⊓ eqn h3 (numeral 1)))))) := by
  intro body alpha Delta cons node code param source target sigma tau q a r b h0 t0 h1 t1 h2 t2 h3 t3 hg hn hs ht hc0 hc1 hc2 hc3
  unfold OriginalDecodedLayerCalibration.layer
  rw [OriginalDecodedLambdaRecurrence.LayerProof.layerIdentity]
  exact StructuralExchangeFields.InternalProof.internalApplication body alpha Delta
    (OriginalDecodedLambdaRecurrence.LayerProof.filled n arity (OriginalDecodedLayerCalibration.guard n))
    (OriginalDecodedLayerCalibration.guard n) cons node code param source target sigma tau q a r b h0 t0 h1 t1 h2 t2 h3 t3
    hg hn hs ht hc0 hc1 hc2 hc3

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.LayerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.LayerProof
