module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionTargets
open UniformCertificateCompletion OriginalTransparentDecoderSelection
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal Program identities need no native calibration assumptions. -/
def ActualOriginalTransparentDecoderLiteralFields : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
    LiteralFields p H G W

/-- No separately selected member, successful source decoding, finite-window
or desired output premise is supplied to this all-vector construction. -/
def ActualOriginalTransparentDecoderCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
      (H G : Program 1) (W : Program 2),
    GlobalSourcePackage.InputsCalibrated n arity p →
    OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
    OriginalVariableLeaves.ContextGuardCalibrated n G →
    OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
    Calibration n arity p H G W

/-- Universal SAME-q retention, not an existential choice of another tuple. -/
def ActualOriginalTransparentDecoderInheritedProperties : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (q : GlobalSourcePackage.Inputs) (G : Program 1),
    GlobalSourcePackage.InputsCalibrated n arity q →
    OriginalVariableLeaves.ContextGuardCalibrated n G → Retained n arity q G

/-- Exactly one initial p and H/G/W are chosen before all runtime inputs. -/
def ActualOriginalTransparentDecoderSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    ∃ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2),
      Properties n arity p H G W

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionTargets
