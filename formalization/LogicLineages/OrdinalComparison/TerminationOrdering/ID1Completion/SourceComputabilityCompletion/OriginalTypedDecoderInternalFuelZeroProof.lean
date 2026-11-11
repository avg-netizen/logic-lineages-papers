module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelZeroSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelZeroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalControlGraphSupportProof OriginalTypedDecoderInternalFuelSupportProof
open InternalTagArithmeticSyntaxProof
open OriginalTypedDecoderInternalFuel OriginalTypedDecoderInternalFuelZeroSupportProof

 theorem actualOriginalTypedInternalWorkFuelZero :
    OriginalTypedDecoderInternalFuelTargets.ActualOriginalTypedInternalWorkFuelZero := by
  intro body alpha count code
  let A := WorkFuelGraph count code
  let P := eqn count z
  let Q := eqn code z
  have hf : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨forward⟩ := zeroReflect count code (withHyp hf P)
    (show Nonempty (Derivation body [P,A] P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨backward⟩ := zeroPreserve count code (withHyp hf Q)
    (show Nonempty (Derivation body [Q,A] Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  simpa only [equalEqn] using
    (show Nonempty (Derivation body [] (A.imp (P.iff Q))) from
      ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
        (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelZeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelZeroProof
