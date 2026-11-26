module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
/-- Only a formula-level finite choice between the TWO ORIGINAL constructor
observations. No new program, encoding or validity predicate. Ordinary ignores
numbered-only metadata because its original constructor has exactly two inputs. -/
def constructor {alpha : Type} (numbered : Bool)
    (raw k f tau base ts extras : OTerm alpha) : Formula alpha :=
  if numbered then programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![k,f,tau,base,ts,extras]
  else graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw f base
/-- Actual node guard and constructor observations force both original head checks. -/
def InternalGuardHeads : Prop := ∀ (n : Nat) (numbered : Bool) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (source target k l f g tau upsilon base dest ts us extras otherExtras node answers param : OTerm alpha),
  Nonempty (Derivation body Delta (constructor numbered source k f tau base ts extras)) →
  Nonempty (Derivation body Delta (constructor numbered target l g upsilon dest us otherExtras)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node answers param)) →
  Nonempty (Derivation body Delta
    (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) f ⊓
     graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) g))
/-- No separate head-validity or encoding-output premises. Guard discharges the
actual decoder domain needed to identify literal encoded equality with raw equality. -/
def InternalGuardedEquality : Prop := ∀ (n : Nat) (numbered : Bool) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (source target k l f g tau upsilon base dest ts us extras otherExtras node answers param : OTerm alpha),
  Nonempty (Derivation body Delta (constructor numbered source k f tau base ts extras)) →
  Nonempty (Derivation body Delta (constructor numbered target l g upsilon dest us otherExtras)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node answers param)) →
  (Nonempty (Derivation body Delta
      (graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (numeral 1) f g)) ↔
   Nonempty (Derivation body Delta (eqn f g)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.Targets
