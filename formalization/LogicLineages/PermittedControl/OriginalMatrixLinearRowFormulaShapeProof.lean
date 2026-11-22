module
public import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaTargets
public import LogicLineages.PermittedControl.PreparedParameterRowsProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixLinearRowFormula
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand PreparedInput PlainPreparedRow)
open SignedRowGuardedTest (Test)

theorem safeAtom (ops : List LowerOperand) (a : NormalForm.Atom) (plain : PlainPreparedRow a.row)
    (bound : ∀ n ∈ NormalForm.rowVariables a.row, n ≤ ops.length) :
    PreparedInput ops (.atom a) := by
  refine ⟨?_,bound⟩
  intro b hb
  have eq : b = a := List.mem_singleton.mp hb
  subst b
  exact plain

theorem safeAnd (ops : List LowerOperand) (p q : NormalForm.Formula)
    (hp : PreparedInput ops p) (hq : PreparedInput ops q) : PreparedInput ops (.conjunction p q) := by
  constructor
  · intro a ha
    exact (List.mem_append.mp ha).elim (hp.1 a) (hq.1 a)
  · intro n hn
    exact (List.mem_append.mp hn).elim (hp.2 n) (hq.2 n)

theorem safeOr (ops : List LowerOperand) (p q : NormalForm.Formula)
    (hp : PreparedInput ops p) (hq : PreparedInput ops q) : PreparedInput ops (.disjunction p q) := by
  constructor
  · intro a ha
    exact (List.mem_append.mp ha).elim (hp.1 a) (hq.1 a)
  · intro n hn
    exact (List.mem_append.mp hn).elim (hp.2 n) (hq.2 n)

theorem safePolarity (ops : List LowerOperand) (p : NormalForm.Formula)
    (hp : PreparedInput ops p) (pos : Bool) : PreparedInput ops (choosePolarity p pos) := by
  cases pos <;> exact hp

theorem safeTruth (ops : List LowerOperand) : PreparedInput ops (.truth) := by
  constructor
  · intro a h
    cases h
  · intro n h
    cases h

theorem safeFalsity (ops : List LowerOperand) : PreparedInput ops (.falsity) := by
  constructor
  · intro a h
    cases h
  · intro n h
    cases h

theorem safeTest (ops : List LowerOperand) (test : Test) (r : NormalForm.Row)
    (plain : PlainPreparedRow r)
    (bound : ∀ n ∈ NormalForm.rowVariables r, n ≤ ops.length) :
    PreparedInput ops (testFormula test r) := by
  cases test with
  | equalZero =>
      have keep : NormalForm.rowVariables (LinearRows.rowScale (-1) r) = NormalForm.rowVariables r := by
        simp only [LinearRows.rowScale,NormalForm.rowVariables,List.map_map,Function.comp_def]
      refine safeAnd ops _ _ (safeAtom ops (.nonnegative r) plain bound)
        (safeAtom ops (.nonnegative (LinearRows.rowScale (-1) r))
          (PreparedProjection.prepared_scale_plain _ _ plain) ?_)
      intro n hn
      exact bound n (keep ▸ hn)
  | nonnegative => exact safeAtom ops _ plain bound
  | positive => exact safeAtom ops (.nonnegative (r.1-1,r.2)) plain bound
  | congruence m => exact safeAtom ops (.divisible (m-1) r) plain bound

end LogicLineages.PermittedControl.OriginalMatrixLinearRowFormula
