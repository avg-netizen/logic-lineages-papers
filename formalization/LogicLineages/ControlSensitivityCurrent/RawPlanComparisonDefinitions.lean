module
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerDefinitions
public import LogicLineages.ControlSensitivityCurrent.RawDerivedCompositionDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanComparison

abbrev OutputCode := (Code × Code) × (Code × Code)

def compareResult (r : PlanCompiler.ResultCode) : Option OutputCode := do
  let (left, right) ← DerivedComposition.aggregate r.1 r.2.2
  let weakRight ← DerivedComposition.wrap true right
  let weakLeft ← DerivedComposition.wrap false left
  return ((right,left),(weakRight,weakLeft))

def compileComparisons (context : List Nat) (code : List PlanCompiler.Instruction) : Option OutputCode :=
  (PlanCompiler.run context code).bind compareResult

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanComparison
