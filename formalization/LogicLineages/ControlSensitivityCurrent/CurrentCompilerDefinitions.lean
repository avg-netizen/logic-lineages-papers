module
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerDefinitions
public import LogicLineages.ControlSensitivityCurrent.RawPlanComparisonTargets
public import LogicLineages.ControlSensitivityCurrent.CompilerCompositionTargets
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentCompiler

open LogicLineages.OrdinalComparison.Source
open RawSourceDAG
open RawSourceDAG.InputCompiler (InputCode)
open RawSourceDAG.PlanComparison (OutputCode compileComparisons)
open RawPlanComparisonTargets (encodeComparison)

/-- The two compiled comparisons, with the exact original shared source tables. -/
def expected {Γ : List Ty} (q : InputNormalization.Input Γ 0) : OutputCode :=
  let p := InputNormalization.normalize .nil q
  (encodeComparison (BooleanCompiler.strictPair p),encodeComparison (BooleanCompiler.weakPair p))

/-- Checked compilation on finite encodings of actual shared inputs. -/
def run (n : Nat) (code : InputCode) : Option OutputCode :=
  let context := List.replicate n 0
  (InputCompiler.run context code).bind (compileComparisons context)

def fallback : OutputCode :=
  let z := DerivedComposition.zeroRaw []
  ((z,z),(z,z))

/-- Total comparison construction. Malformed encodings return two fixed closed pairs. -/
def compile (p : Nat × InputCode) : OutputCode :=
  (run p.1 p.2).getD fallback

end LogicLineages.ControlSensitivityCurrent.CurrentCompiler
