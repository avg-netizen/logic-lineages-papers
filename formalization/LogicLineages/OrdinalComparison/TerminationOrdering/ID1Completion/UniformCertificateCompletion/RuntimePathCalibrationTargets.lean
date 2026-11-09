module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePathCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePathCalibrationTargets
open Source
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Universal construction from globally calibrated ORIGINAL inputs. The SAME
Data, window AST and old vertex precede every source window, Gamma and raw
coordinate. The literal global window and typed guards remain unchanged.
This is native all-input calibration, not an existential complete source
selection or an internal lift/ID1 theorem. No successful decoder, nonzero
output, typed-input or source-window premise restricts the conclusion. -/
def ActualOriginalRuntimePathCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data)
    (window : Program 1) (oldVertex : Program 5),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  Path.windowCalibrated n window →
  (∀ v : List.Vector Nat 5, evaluate oldVertex v = RuntimeVertex.value n arity v) →
  RuntimePathCalibration.Calibrated n arity data window oldVertex

/-- The COMPLETE old vertex output is retained on every inactive input,
without calibration or successful decoding hypotheses. -/
def ActualOriginalRuntimeVertexFallback : Prop :=
  ∀ (data : Data) (window : Program 1) (oldVertex : Program 5)
    (v : List.Vector Nat 5),
  evaluate (Path.activation data window) v = 0 →
  evaluate (RuntimePathCalibration.vertex data window oldVertex) v = evaluate oldVertex v

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePathCalibrationTargets
