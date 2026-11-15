module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Every raw old-table code; exact-one Bool interpretation, default []/false unchanged. -/
def NativeRows : Prop := ∀ (n bound previous : Nat),
  evaluate (nextRow n) (List.Vector.ofFn ![bound,previous]) =
    NumberedMultisetNumeric.numbersNumber
      ((List.range (bound+1)).map (fun value =>
        (NumberedCodeParserTable.codeNext n
          (((NumberedMultisetNumeric.decodeNumbers previous).getD []).map (fun v => v == 1)) value).toNat))
/-- Exact original fuel-zero replicate and ascending finite table, not a raw-cache surrogate. -/
def NativeTable : Prop := ∀ (n bound fuel : Nat),
  evaluate (tableProgram n) (List.Vector.ofFn ![fuel,bound]) =
    NumberedMultisetNumeric.numbersNumber
      ((NumberedCodeParserTable.codeTable n bound fuel).map Bool.toNat)
/-- Entire actual row contains the actual step output at each object-language bounded
index. Length/order, singleton, predecessor and intermediate outputs are internal duties. -/
def InternalRowLookup : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (bound previous next index value : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (nextRow n) next bound previous)) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess index (suc bound))) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value index next)) →
  Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderStep.step n) value previous index))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.Targets
