module
public import LogicLineages.OrdinalComparison.SourcePlanInsertionCodeDefinitions
public import LogicLineages.OrdinalComparison.ParametricScalingPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceScalingSpineCode
open SourcePlanSpineCode SourcePrimitiveForestCode
abbrev ScaleState := Nat × Nat × List Instruction

def advance (s : ScaleState) : ScaleState :=
  (shiftPort 1 s.1,1,(2,1,1,shiftPort 1 s.2.1)::SourcePlanInsertionCode.insert 0 1 s.2.2)
def build (e a out : Nat) (is : List Instruction) : List Instruction :=
  let s := advance^[e] (a,out,is)
  List.replicate e (4,0,0,0) ++ (1,s.1,s.2.1,0)::s.2.2
end LogicLineages.OrdinalComparison.Source.SourceScalingSpineCode
