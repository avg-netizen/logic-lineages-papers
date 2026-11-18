module
public import LogicLineages.ControlSensitivityCurrent.CurrentProbeCodeDefinitions
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentProbeCodeTargets

open LogicLineages.OrdinalComparison.Source GroundEquivalence RawSourceDAG CurrentProbeCode

def ExactClosing : Prop := ∀ Γ τ (hg : ∀ σ ∈ Γ, σ = Ty.ground) (d : Input Γ τ),
    closeRaw (encode ⟨Γ,τ,d⟩) = encode ⟨[],τ,AbsoluteProbeDAG.closeInput hg d⟩
def ExactProbe : Prop := ∀ Γ τ (d : Input Γ τ) (x : Variable Γ .ground),
    probeRaw (encode ⟨Γ,τ,d⟩) (variableIndex x) = encode ⟨Γ,.ground,AbsoluteProbeDAG.probeInput d x⟩
def Effective : Prop := Primrec closeRaw ∧ Primrec₂ probeRaw
end LogicLineages.ControlSensitivityCurrent.CurrentProbeCodeTargets
