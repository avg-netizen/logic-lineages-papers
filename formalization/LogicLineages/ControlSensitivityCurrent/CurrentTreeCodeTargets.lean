module
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeCodeDefinitions
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentTreeCodeTargets

open RawSourceDAG CurrentTreeCode
open LogicLineages.OrdinalComparison.Source GroundEquivalence

def Exact : Prop := ∀ (Γ : List Ty) (τ : Ty) (d : Input Γ τ),
  expand (encode ⟨Γ,τ,d⟩) = SyntaxCode.encodeTerm d.term

def Effective : Prop := Primrec expand

end LogicLineages.ControlSensitivityCurrent.CurrentTreeCodeTargets
