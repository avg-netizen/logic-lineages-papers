module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealFiniteDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealFinite.Targets
open RankedParse ProfileAutomatonEncoding RankedIdealCompletion

def SuccessorsExact : Prop := ∀ (M : Machine) [DecidableEq M.State] x y,
  y ∈ successors M x ↔ Epsilon M x y

def ClosureExact : Prop := ∀ (M : Machine) [DecidableEq M.State] S q,
  q ∈ close M S ↔ Closure M S q

def EvaluationExact : Prop := ∀ (M : Machine) [DecidableEq M.State] t q,
  q ∈ evaluate M t ↔ Run M t q

def AcceptanceExact : Prop := ∀ (M : Machine) [DecidableEq M.State] t,
  accepts M t = true ↔ ∃ u, Homeomorphic t u ∧ M.accept (machineRun M u) = true
end LogicLineages.ModelsAlgebra.Forests.RankedIdealFinite.Targets
