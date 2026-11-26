module
public import LogicLineages.ControlSensitivityCurrent.RawCheckedCompositionDefinitions
public import LogicLineages.OrdinalComparison.WWAbsoluteProbeDAGDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentProbeCode

open LogicLineages.OrdinalComparison.Source
open RawSourceDAG CheckedComposition Operations

def closeNode (a : Node) : Node :=
  if a.2.2.1 = 0 ∧ a.1.length ≤ a.2.2.2.getD 0 0 then (a.1,0,3,[]) else a

def closeRaw (d : Code) : Code := ([],d.2.1.map closeNode,d.2.2)

def probeRaw (d : Code) (x : Nat) : Code :=
  let τ := d.2.2.2
  (d.1,
    rawNode 0 1 [τ,0,2] :: rawNode (SyntaxCode.arrowCode τ 0) 2 [τ,0,0] ::
    ([τ],0,3,[]) :: rawNode τ 1 [0,1,0] :: rawNode 0 0 [x] ::
    rawNode (SyntaxCode.arrowCode 0 τ) 2 [0,τ,d.2.2.1] :: insertTable d.2.1,0,0)

end LogicLineages.ControlSensitivityCurrent.CurrentProbeCode
