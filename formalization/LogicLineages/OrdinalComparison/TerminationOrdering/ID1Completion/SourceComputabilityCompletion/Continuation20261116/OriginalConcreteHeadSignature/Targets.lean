module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- All raw naturals, including n=0 and decoder failures. This is the existing
original headSignatureValue, not a new meaning assigned to the desired AST. -/
def NativeSignature : Prop := ∀ (n : Nat) (arity : Fin n → Nat),
  OriginalTypedDecoder.HeadSignatureCalibrated n arity (signature n arity)
/-- Exact valid factor at actual queried output witnesses. No native calibration
is usable as an internal inference and no decoded-image restriction is supplied. -/
def InternalValidSignature : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw result argumentsCode packed : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 Continuation20261114.OriginalHeadResult.headResult result raw)) →
  Nonempty (Derivation body Delta (graph1 (arguments n arity) argumentsCode raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed result argumentsCode)) →
  (Nonempty (Derivation body Delta (graph1 (signature n arity) (suc packed) raw)) ↔
   Nonempty (Derivation body Delta (graph1 (Continuation20261115.OriginalHeadDecoderValidity.check n) (suc z) raw)))
/-- Complete zero/failure factor; success output is always a successor. -/
def InternalInvalidSignature : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (raw : OTerm alpha),
  (Nonempty (Derivation body Delta (graph1 (signature n arity) z raw)) ↔
   Nonempty (Derivation body Delta (graph1 (Continuation20261115.OriginalHeadDecoderValidity.check n) z raw)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.Targets
