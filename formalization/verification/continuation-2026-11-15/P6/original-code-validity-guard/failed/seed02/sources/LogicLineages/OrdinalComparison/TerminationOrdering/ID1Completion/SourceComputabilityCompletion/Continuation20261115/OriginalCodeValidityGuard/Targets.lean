module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- All raw values, including failed decoding and the original round-trip filter. -/
def NativeValidity : Prop := ∀ (n raw : Nat),
  evaluate (check n) (List.Vector.ofFn ![raw]) =
    (NumberedNumericDecoding.decodeCode n raw).isSome.toNat
/-- Original finite-table acceptance persists for one actual fuel successor, at any
object-language bounded index. No native image, row length, selector bounds or
monotonicity premises are admitted; those are internal induction duties. -/
def InternalTablePersistence : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (fuel bound previous next index : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph2 (OriginalCodeDecoderTable.tableProgram n) previous fuel bound)) →
  Nonempty (Derivation body Delta
    (graph2 (OriginalCodeDecoderTable.tableProgram n) next (suc fuel) bound)) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess index (suc bound))) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) index previous)) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) index next))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Targets
