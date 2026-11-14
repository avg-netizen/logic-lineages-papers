module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def NativeHeadEncoding : Prop := ∀ (n : Nat) (h : NumberedAuxiliaryCoding.HeadCode (Fin n)),
  evaluate encodeHead (List.Vector.ofFn ![NumberedLeastCodeRepresentative.headNumber h]) = Encodable.encode h
/-- Lists use the same cons pairing extensionally, not definitionally. -/
def NativeTypeListEncoding : Prop := ∀ ts : List Source.Ty,
  NumberedLeastCodeRepresentative.typesNumber ts = Encodable.encode ts
/-- Real internal dispatch and payload composition for every supported raw tag.
There is no semantic decoding premise or native reflection in this law. -/
def InternalTagFactor : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (tag : Fin 6) (raw payload out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral tag.val) payload)) →
  (Nonempty (Derivation body Delta (graph1 encodeHead out raw)) ↔
   Nonempty (Derivation body Delta (graph1 (branchCode tag.val) out payload)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.Targets
