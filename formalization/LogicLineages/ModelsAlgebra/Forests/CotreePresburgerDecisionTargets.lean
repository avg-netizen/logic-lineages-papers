module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerDecisionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerDecision.Targets
open CotreePresburgerUnit

def QuantifierEliminationExact : Prop := ∀ n (p : Formula n) (v : Fin n → Int),
  evalQF (quantifierFree p) v = true ↔ Realize p v

def EvaluationExact : Prop := ∀ n (p : Formula n) (v : Fin n → Int),
  evaluate p v = true ↔ Realize p v

def ClosureExact : Prop := ∀ n (p : Formula n),
  Realize (close p) Fin.elim0 ↔ ∃ v : Fin n → Nat, Realize p (fun i => (v i : Int))

def SatisfiabilityExact : Prop := ∀ n (p : Formula n),
  satisfiable p = true ↔ ∃ v : Fin n → Nat, Realize p (fun i => (v i : Int))
end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerDecision.Targets
