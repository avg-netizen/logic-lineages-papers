module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuardsTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuardsProof
open NormalForm ShiftedInputGuards

theorem less_eval (a b : Input) (ν : Nat → Nat) :
    (less a b).eval ν ↔ value a ν < value b ν := by
  simp only [less, Formula.eval, Atom.eval, rowValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Summand.term, Term.value, one_mul, neg_one_mul, add_zero,
    value]
  omega

theorem bound_eval (a : Input) (c : Nat) (ν : Nat → Nat) :
    (bound c a).eval ν ↔ c ≤ value a ν := by
  by_cases hc : c = 0
  · simp [hc, bound, Formula.eval]
  · simp only [bound, hc, if_false, Formula.eval, Atom.eval, rowValue,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Summand.term,
      Term.value, one_mul, add_zero, value]
    omega

theorem equal_eval (a b : Input) (ν : Nat → Nat) :
    (equal a b).eval ν ↔ value a ν = value b ν := by
  simp only [equal, Formula.eval, less_eval]
  omega

theorem actualAtomicComparisons : ShiftedInputGuardsTargets.ActualAtomicComparisons :=
  ⟨less_eval, bound_eval⟩

theorem actualGuardCompilation : ShiftedInputGuardsTargets.ActualGuardCompilation := by
  intro xs p ν
  induction p with
  | truth => rfl
  | falsity => rfl
  | eq i j => exact equal_eval _ _ _
  | lt i j => exact less_eval _ _ _
  | bound c i => exact bound_eval _ _ _
  | neg p ih => exact not_congr ih
  | conj p q ihp ihq => exact and_congr ihp ihq
  | disj p q ihp ihq => exact or_congr ihp ihq

private theorem less_linear (a b : Input) (i : Nat) :
    LinearRows.isLinear i (less a b) = true := by
  simp [less, LinearRows.isLinear, LinearRows.atoms, LinearRows.rowLinear,
    LinearRows.summandLinear, Atom.row]

private theorem equal_linear (a b : Input) (i : Nat) :
    LinearRows.isLinear i (equal a b) = true := by
  have h₁ := less_linear a b i
  have h₂ := less_linear b a i
  simpa only [equal, LinearRows.isLinear, LinearRows.atoms, List.all_append] using
    Bool.and_eq_true_iff.mpr ⟨h₁, h₂⟩

private theorem bound_linear (a : Input) (c i : Nat) :
    LinearRows.isLinear i (bound c a) = true := by
  by_cases hc : c = 0 <;>
    simp [bound, hc, LinearRows.isLinear, LinearRows.atoms, LinearRows.rowLinear,
      LinearRows.summandLinear, Atom.row]

theorem literalGuardLinearity : ShiftedInputGuardsTargets.LiteralGuardLinearity := by
  intro xs p i
  induction p with
  | truth => rfl
  | falsity => rfl
  | eq j k => exact equal_linear _ _ _
  | lt j k => exact less_linear _ _ _
  | bound c j => exact bound_linear _ _ _
  | neg p ih => exact ih
  | conj p q ihp ihq =>
      simpa only [compile, LinearRows.isLinear, LinearRows.atoms, List.all_append] using
        Bool.and_eq_true_iff.mpr ⟨ihp, ihq⟩
  | disj p q ihp ihq =>
      simpa only [compile, LinearRows.isLinear, LinearRows.atoms, List.all_append] using
        Bool.and_eq_true_iff.mpr ⟨ihp, ihq⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuardsProof
