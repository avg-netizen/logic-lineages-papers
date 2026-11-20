module
public import Init

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateFinitePureProof

universe u

private theorem atEqual {X : Sort u} (xs ys : Fin 6 → X) {i j : Fin 6}
    (ij : i = j) (same : xs j = ys j) : xs i = ys i :=
  Eq.trans (congrArg xs ij) (Eq.trans same (Eq.symm (congrArg ys ij)))

/-- Pure finite tuple bookkeeping with no graph/formula dependencies.
No tactic-level substitution is used on the Fin coordinate. -/
theorem retainedEqual {X : Sort u} (xs ys : Fin 6 → X)
    (first : xs 1 = ys 1) (second : xs 2 = ys 2) (third : xs 3 = ys 3)
    (i : Fin 6) (keep : i = 1 ∨ i = 2 ∨ i = 3) : xs i = ys i :=
  Or.elim keep
    (fun h => atEqual xs ys h first)
    (fun h => Or.elim h (fun e => atEqual xs ys e second) (fun e => atEqual xs ys e third))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateFinitePureProof
