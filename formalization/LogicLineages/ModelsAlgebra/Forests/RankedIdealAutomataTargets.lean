module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealAutomataDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealAutomata.Targets
open RankedParse ProfileAutomatonEncoding

def ClosureExact : Prop := ∀ A S q, q ∈ close A S ↔ Closure A S q

def EvaluationExact : Prop := ∀ A t q, q ∈ evaluate A t ↔ Run A t q

def RunCalibration : Prop := ∀ A t, machineRun (determinize A) t = evaluate A t

def DeterminizationExact : Prop := ∀ A t,
  (determinize A).accept (machineRun (determinize A) t) = true ↔ Accepts A t
end LogicLineages.ModelsAlgebra.Forests.RankedIdealAutomata.Targets
