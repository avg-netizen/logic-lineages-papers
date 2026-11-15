module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- All numeric tables/raw codes. Missing table slots are false; only numeric one
is true, not arbitrary nonzero. decodeNumbers uses its original default []. -/
def NativeCodeNext : Prop := ∀ (n table rawCode : Nat),
  evaluate (step n) (List.Vector.ofFn ![table,rawCode]) =
    (NumberedCodeParserTable.codeNext n
      (((NumberedMultisetNumeric.decodeNumbers table).getD []).map (fun value => value == 1)) rawCode).toNat

def allowed {alpha : Type} (n : Nat) (table tagValue payloadValue first second head : OTerm alpha) : Formula alpha :=
  (eqn tagValue (numeral 0) ⊔ eqn tagValue (numeral 3)) ⊔
  ((eqn tagValue (numeral 1) ⊓ graph2 InternalRawListRecursion.lookup (numeral 1) first table) ⊔
  (((eqn tagValue (numeral 2) ⊔ eqn tagValue (numeral 7)) ⊓
      (graph2 InternalRawListRecursion.lookup (numeral 1) first table ⊓
       graph2 InternalRawListRecursion.lookup (numeral 1) second table)) ⊔
  ((eqn tagValue (numeral 4) ⊓
      (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head ⊓
       graph2 InternalRawListRecursion.lookup (numeral 1) first table)) ⊔
  ((eqn tagValue (numeral 5) ⊓
      ((graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head ⊓
        graph2 InternalRawListRecursion.lookup (numeral 1) first table) ⊓
        graph2 InternalRawListRecursion.lookup (numeral 1) second table)) ⊔
    (eqn tagValue (numeral 6) ⊓ eqn payloadValue (numeral 0))))))
/-- Actual field observations only, not assumptions that children or heads are valid.
The formula retains all eight original constructors and excludes every unknown tag. -/
def InternalAcceptedBranches : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (table rawCode tagValue payloadValue first second head : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawCode tagValue payloadValue)) →
  Nonempty (Derivation body Delta (graph2 firstField first table rawCode)) →
  Nonempty (Derivation body Delta (graph2 secondField second table rawCode)) →
  Nonempty (Derivation body Delta (graph2 headField head table rawCode)) →
  (Nonempty (Derivation body Delta (graph2 (step n) (numeral 1) table rawCode)) ↔
    Nonempty (Derivation body Delta (allowed n table tagValue payloadValue first second head)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderStep.Targets
