module

public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCompositionDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmetic

open FirstOrder Language

/-- Check the actual base graph at the entry with index zero. Universal
guarding is legitimate because the beta graph is total and single-valued. -/
def initialGraph {n : Nat} {α : Type} (f : Formula (Fin (n + 1)))
    (a b : Term α) (params : Fin n → Term α) : Formula α :=
  forallFin ((betaFormula (a.relabel Sum.inl) (b.relabel Sum.inl) zeroTerm
      (.var (.inr (0 : Fin 1)))).imp
    (applyGraph f (.var (.inr 0)) (fun i => (params i).relabel Sum.inl)))

/-- The quantified variables are the step index, previous value, next value.
The graph receives exactly the original evaluator's j,previous,parameters order. -/
def stepGraph {n : Nat} {α : Type} (g : Formula (Fin (n + 3)))
    (a b t : Term α) (params : Fin n → Term α) : Formula α :=
  let j : Term (α ⊕ Fin 3) := .var (.inr 0)
  let previous : Term (α ⊕ Fin 3) := .var (.inr 1)
  let next : Term (α ⊕ Fin 3) := .var (.inr 2)
  let A := a.relabel Sum.inl
  let B := b.relabel Sum.inl
  forallFin (((lessFormula j (t.relabel Sum.inl) ⊓ betaFormula A B j previous) ⊓
    betaFormula A B (succTerm j) next).imp
    (applyGraph g next (Fin.cons j (Fin.cons previous
      (fun i => (params i).relabel Sum.inl)))))

/-- The two existential values are the beta code components. All checks are
ordinary arithmetic formulas. Free index0 is output, index1 is recursion
counter, remaining indices are the unchanged source parameters. -/
def recursionGraph {n : Nat} (f : Formula (Fin (n + 1)))
    (g : Formula (Fin (n + 3))) : Formula (Fin (n + 2)) :=
  let A : Term (Fin (n + 2) ⊕ Fin 2) := .var (.inr 0)
  let B : Term (Fin (n + 2) ⊕ Fin 2) := .var (.inr 1)
  let T : Term (Fin (n + 2) ⊕ Fin 2) := .var (.inl 1)
  let params : Fin n → Term (Fin (n + 2) ⊕ Fin 2) :=
    fun i => .var (.inl i.succ.succ)
  existsFin ((initialGraph f A B params ⊓ stepGraph g A B T params) ⊓
    betaFormula A B T (.var (.inl 0)))

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmetic
