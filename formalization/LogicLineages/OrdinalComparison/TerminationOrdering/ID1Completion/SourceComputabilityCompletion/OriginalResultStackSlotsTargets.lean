module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
def Boundary : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (count initialList suffix joined value : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count initialList)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined initialList suffix)) →
 Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode value suffix)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value count joined))
/-- No desired selector or offset graph premise: actual length/append/cons only. -/
def OneChild : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (count initialList suffix joined value old : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count initialList)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined initialList suffix)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode suffix value old)) →
 Nonempty (Derivation body Delta
   (graph3 OriginalHereditaryResultStackProgram.firstSlot value (suc z) count joined ⊓
    graph3 OriginalHereditaryResultStackProgram.secondSlot z (suc z) count joined))
def TwoChildren : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (count initialList suffix joined first second tail old : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count initialList)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined initialList suffix)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode suffix second tail)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail first old)) →
 Nonempty (Derivation body Delta
   (graph3 OriginalHereditaryResultStackProgram.firstSlot first (suc (suc z)) count joined ⊓
    graph3 OriginalHereditaryResultStackProgram.secondSlot second (suc (suc z)) count joined))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsTargets
