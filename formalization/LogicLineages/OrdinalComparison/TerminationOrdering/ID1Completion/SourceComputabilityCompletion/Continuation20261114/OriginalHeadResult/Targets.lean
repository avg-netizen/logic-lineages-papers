module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def NativeHeadResult : Prop := ∀ (n : Nat) (h : NumberedAuxiliaryCoding.HeadCode (Fin n)),
  evaluate headResult (List.Vector.ofFn ![NumberedLeastCodeRepresentative.headNumber h]) =
    Encodable.encode (Source.SourceMarkedSyntax.headResult (NumberedAuxiliaryDecoding.decodeHead h))
/-- Genuine internal dispatch and actual type-construction graphs, not reflection. -/
def InternalTagFactor : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (tag : Fin 6) (raw payload out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral tag.val) payload)) →
  (Nonempty (Derivation body Delta (graph1 headResult out raw)) ↔
   Nonempty (Derivation body Delta (graph1 (branchResult tag.val) out payload)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.Targets
