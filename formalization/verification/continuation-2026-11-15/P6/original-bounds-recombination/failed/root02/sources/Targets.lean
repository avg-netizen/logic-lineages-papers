module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual original recombine, on every raw code and encoded child-answer list.
No decoded-image restriction: source-code failure maps to None=0; list parsing
uses its literal getD[] and every numeric answer is unpaired in order. -/
def NativeRecombine : Prop := ∀ (n : Nat) (v : List.Vector Nat 2),
  evaluate (recombine n) v =
    ((NumberedNumericDecoding.decodeCode n (v.get 0)).map (fun code =>
      Encodable.encode (NumberedSyntaxBoundsPrimrecSupportProof.recombine code
        (((NumberedMultisetNumeric.decodeNumbers (v.get 1)).getD []).map Nat.unpair)))).getD 0
/-- Empty actual raw list folds to the original pair (0,0) encoding0. -/
def InternalNil : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)),
  Nonempty (Derivation body Delta (graph1 collect (numeral 0) (numeral 0)))
/-- Exact actual cons recurrence, including arbitrary bound-pair values and
original list order. Tail output is an actual graph observation, not native image. -/
def InternalCons : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw head tail tailValue out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)) →
  Nonempty (Derivation body Delta (graph1 collect tailValue tail)) →
  (Nonempty (Derivation body Delta (graph1 collect out raw)) ↔
   Nonempty (Derivation body Delta (graph2 merge out head tailValue)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalBoundsRecombination.Targets
