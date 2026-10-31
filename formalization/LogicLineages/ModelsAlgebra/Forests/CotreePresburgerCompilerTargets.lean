module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCompilerDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCompiler.Targets
open FirstOrder Language

def CompilationExact : Prop := ∀ (α : Type) n k (p : presburger.BoundedFormula α n)
    (e : α ⊕ Fin n → Fin k) (v : Fin k → Nat),
  CotreePresburgerDecision.Realize (compile p e) (fun i => (v i : Int)) ↔
    p.Realize (fun a => v (e (.inl a))) (fun i => v (e (.inr i)))

def FormulaExact : Prop := ∀ n (p : presburger.Formula (Fin n)) (v : Fin n → Nat),
  CotreePresburgerDecision.Realize (ofFormula p) (fun i => (v i : Int)) ↔
    FirstOrder.Language.Formula.Realize p v

def EvaluationExact : Prop := ∀ n (p : presburger.Formula (Fin n)) (v : Fin n → Nat),
  evaluate p v = true ↔ FirstOrder.Language.Formula.Realize p v

def SatisfiabilityExact : Prop := ∀ n (p : presburger.Formula (Fin n)),
  satisfiable p = true ↔ ∃ v : Fin n → Nat, FirstOrder.Language.Formula.Realize p v
end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCompiler.Targets
