module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterNativeCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterNativeCalibrationTargets
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Close the native calibration of the SAME final selected Data, rather
than introducing a second selection. The BottomRepresentative readyData
conclusion already includes its one membership normalization. -/
def ActualOriginalOuterSelectedDataCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (base : Data) (window : Program 1),
  InternalOriginalUniformDescentSelection.Calibrated n arity base →
  Path.windowCalibrated n window →
  InternalOriginalUniformDescentSelection.Calibrated n arity
    (OuterSelection.data base window)

/-- Original scalar/typed source semantics for ALL raw context/Object inputs.
Global fallback Programs remain replaceable inputs and retain their whole
original inactive outputs. This is calibration of an explicit construction,
not an existential selection of a complete calibrated source package. -/
def ActualOriginalOuterScalarTypedCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (base : Data) (window : Program 1)
    (oldScalar : Program 2) (oldTyped : Program 3),
  InternalOriginalUniformDescentSelection.Calibrated n arity base →
  Path.windowCalibrated n window →
  (∀ v : List.Vector Nat 2, evaluate oldScalar v = ContextUniform.scalarValue n arity v) →
  (∀ v : List.Vector Nat 3, evaluate oldTyped v = JointGammaTyped.typedValue n arity v) →
  OuterNativeCalibration.ScalarTypedCalibrated n arity base window oldScalar oldTyped

/-- The literal original validity/Gamma/tag layers remain in the target.
All three native fields are calibrated, including the unchanged complete
old application checker. No native equality is an internal derivation. -/
def ActualOriginalOuterBaseComputabilityCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (base : Data) (window : Program 1)
    (old : JointGammaComputability.Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity base →
  Path.windowCalibrated n window →
  JointGammaComputability.Calibrated old n arity →
  JointGammaComputability.Calibrated
    (Outer.baseComputability old (OuterSelection.data base window) window) n arity

/-- Pure AST fallback preservation without ANY calibration or decoding
hypotheses. Zero activation retains the COMPLETE old scalar/typed output,
including malformed-context and nonclosed-window inputs. -/
def ActualOriginalOuterScalarTypedFallback : Prop :=
  ∀ (data : Data) (rawScalar : Program 2) (window : Program 1)
    (oldScalar : Program 2) (oldTyped : Program 3),
  (∀ v : List.Vector Nat 2,
    evaluate window (List.Vector.ofFn ![v.get 0]) = 0 →
    evaluate (Outer.scalar rawScalar window oldScalar) v = evaluate oldScalar v) ∧
  (∀ v : List.Vector Nat 3,
    evaluate window (List.Vector.ofFn ![v.get 0]) = 0 →
    evaluate (Outer.typed data window oldTyped) v = evaluate oldTyped v)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterNativeCalibrationTargets
