module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildContentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryResultStackProgramDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseChildSlotsTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)

/-- The completed child values occur backwards below the deletion prefix in
stack order. Their forward lookups, not an equality of the two rows, identify
the actual runtime slots. Actual original arity limits the child count to 0/1/2;
the old stack is arbitrary and is excluded by the literal counters and lengths.
No value is asserted to equal Q or a completed evaluator observation. -/
def ActualSlots : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (raw childCount deletionCount forwardRow backwardRow deletionPrefix produced old results first second : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) childCount raw)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph childCount forwardRow)) →
  Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse backwardRow forwardRow)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletionCount deletionPrefix)) →
  Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced deletionPrefix backwardRow)) →
  Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results produced old)) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z forwardRow)) →
  Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (numeral 1) forwardRow)) →
  Nonempty (Derivation body Delta
    (graph3 OriginalHereditaryResultStackProgram.firstSlot first childCount deletionCount results ⊓
     graph3 OriginalHereditaryResultStackProgram.secondSlot second childCount deletionCount results))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseChildSlotsTargets
