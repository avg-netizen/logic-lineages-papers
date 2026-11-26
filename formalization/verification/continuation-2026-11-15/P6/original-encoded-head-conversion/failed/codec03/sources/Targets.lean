module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Every natural input uses the ORIGINAL Encodable HeadCode instance.
Invalid Bool/Fin payloads yield raw0, exactly the explicit Option default. -/
def NativeConversion : Prop := ∀ (n raw : Nat),
  evaluate (convert n) (List.Vector.ofFn ![raw]) =
    ((Encodable.decode (α := NumberedAuxiliaryCoding.HeadCode (Fin n)) raw).map
      NumberedLeastCodeRepresentative.headNumber).getD 0
/-- Genuine internal inverse on syntactically valid raw heads. All finite
sum arithmetic and witness recovery are internal; no native reflection.
The source validity premise is explicit, not inferred for arbitrary raw input. -/
def InternalInverse : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (n : Nat) (raw encoded : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) raw)) →
  Nonempty (Derivation body Delta (graph1 Continuation20261114.OriginalHeadEncodingBridge.encodeHead encoded raw)) →
  Nonempty (Derivation body Delta (graph1 (convert n) raw encoded))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.Targets
