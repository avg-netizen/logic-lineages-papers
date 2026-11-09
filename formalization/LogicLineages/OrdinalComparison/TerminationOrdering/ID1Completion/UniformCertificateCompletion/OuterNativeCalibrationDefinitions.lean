module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterNativeCalibration
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Native all-input calibration of the LITERAL original object dispatches.
The tuple is exactly OuterSelection.data: the full-spine representative,
bottom parameter, bottom representative, then membership normalized ONCE.
The same globally chosen base/window precede every raw context and Object.
No canonical-context, successful-input or nonzero-output restriction occurs. -/
structure ScalarTypedCalibrated (n : Nat) (arity : Fin n → Nat)
    (base : Data) (window : Program 1) (oldScalar : Program 2)
    (oldTyped : Program 3) : Prop where
  scalar : ∀ v : List.Vector Nat 2,
    evaluate (Outer.scalar
        (SourceComputabilityCompletion.RawScalar.checker (OuterSelection.data base window))
        window oldScalar) v = ContextUniform.scalarValue n arity v
  typed : ∀ v : List.Vector Nat 3,
    evaluate (Outer.typed (OuterSelection.data base window) window oldTyped) v =
      JointGammaTyped.typedValue n arity v

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterNativeCalibration
