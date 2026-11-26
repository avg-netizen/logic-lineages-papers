module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLayerCalibration.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLayerCalibration.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Exact original successful Node/Window decode predicate, every vector. -/
def NativeGuard : Prop := ∀ (n : Nat) (v : List.Vector Nat 3),
  evaluate (guard n) v = TransparentExchangeLayer.validValue n v
/-- Literal concrete optional layer on all vectors, including malformed nodes,
windows, answer lists and non-Boolean answer payloads. No suppliers assumed. -/
def NativeLayer : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 3),
  evaluate (layer n arity) v = ExchangeNumericSuppliers.layerValue n arity v
/-- Original pair projections and validity formula, paid internally. The type
list has no extra restriction; this is syntax decoding, not typed acceptance. -/
def InternalGuard : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (node answers param source target symbols types : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbols types)) →
  (Nonempty (Derivation body Delta (graph3 (guard n) (numeral 1) node answers param)) ↔
   Nonempty (Derivation body Delta
    ((graph1 (OriginalCodeValidityGuard.check n) (numeral 1) source ⊓
      graph1 (OriginalCodeValidityGuard.check n) (numeral 1) target) ⊓
      OriginalDecodedWindowValidity.Targets.boundedMembers n symbols)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLayerCalibration.Targets
