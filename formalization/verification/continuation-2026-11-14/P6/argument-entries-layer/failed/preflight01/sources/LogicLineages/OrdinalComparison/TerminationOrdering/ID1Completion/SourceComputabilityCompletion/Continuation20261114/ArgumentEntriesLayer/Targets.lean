module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def NativeLayer : Prop :=
  (∀ (n : Nat) (c : NumberedAuxiliaryCoding.Code (Fin n))
      (tail : Option (List (Source.Ty × NumberedAuxiliaryCoding.Code (Fin n)))),
    evaluate step (List.Vector.ofFn ![NumberedLeastCodeRepresentative.codeNumber c,Encodable.encode tail]) =
      Encodable.encode (semanticStep c tail)) ∧
  (∀ (n : Nat) (c : NumberedAuxiliaryCoding.Code (Fin n))
      (answers : List (Option (List (Source.Ty × NumberedAuxiliaryCoding.Code (Fin n))))),
    evaluate recombine (List.Vector.ofFn ![NumberedLeastCodeRepresentative.codeNumber c,
      NumberedMultisetNumeric.encodeNumbers (answers.map Encodable.encode)]) =
      Encodable.encode (some (semanticStep c (answers.getD 1 none))))
def InternalNil : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw tail : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 6) (numeral 0))) →
  Nonempty (Derivation body Delta (graph2 step (numeral 1) raw tail))
def InternalConsFailure : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw tau q rest : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau q rest)) →
  Nonempty (Derivation body Delta (graph2 step (numeral 0) raw (numeral 0)))
def InternalConsSuccess : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw tau q rest tail entryCode listCode : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau q rest)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entryCode tau q)) →
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode listCode entryCode tail)) →
  Nonempty (Derivation body Delta (graph2 step (suc listCode) raw (suc tail)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.Targets
