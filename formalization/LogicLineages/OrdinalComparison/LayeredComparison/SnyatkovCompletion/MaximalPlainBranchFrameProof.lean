module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProof
open NormalForm MaximalPlainBranch

theorem lowerGuard_eval (i c : Nat) (ν : Nat → Nat) :
    (lowerGuard i c).eval ν ↔ c ≤ ν i := by
  simp only [lowerGuard, Formula.eval, Atom.eval, rowValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Summand.term, Term.value, one_mul, add_zero]
  omega

theorem maximumGuard_eval (i j : Nat) (ν : Nat → Nat) :
    (maximumGuard i j).eval ν ↔ ν j ≤ ν i := by
  simp only [maximumGuard, Formula.eval, Atom.eval, rowValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Summand.term, Term.value, one_mul, neg_one_mul, add_zero, zero_add]
  omega

private theorem maxima_eval (i : Nat) (xs : List Nat) (ν : Nat → Nat) :
    (xs.foldr (fun j rest => Formula.conjunction (maximumGuard i j) rest) .truth).eval ν ↔
      ∀ j ∈ xs, ν j ≤ ν i := by
  induction xs with
  | nil => simp [Formula.eval]
  | cons j xs ih => simp only [List.foldr_cons, Formula.eval, maximumGuard_eval, ih,
      List.mem_cons, forall_eq_or_imp]

theorem literalFrame : MaximalPlainBranchTargets.LiteralFrame := by
  intro i p ν
  exact and_congr (lowerGuard_eval i (cutoff p) ν) (maxima_eval i p.variables ν)

theorem lowerGuard_linear (i c k : Nat) : LinearRows.isLinear k (lowerGuard i c) = true := by
  simp [lowerGuard, LinearRows.isLinear, LinearRows.atoms, LinearRows.rowLinear,
    LinearRows.summandLinear, Atom.row]

theorem maximumGuard_linear (i j k : Nat) : LinearRows.isLinear k (maximumGuard i j) = true := by
  simp [maximumGuard, LinearRows.isLinear, LinearRows.atoms, LinearRows.rowLinear,
    LinearRows.summandLinear, Atom.row]

private theorem maxima_linear (i k : Nat) (xs : List Nat) :
    LinearRows.isLinear k
      (xs.foldr (fun j rest => Formula.conjunction (maximumGuard i j) rest) .truth) = true := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
      simpa only [List.foldr_cons, LinearRows.isLinear, LinearRows.atoms, List.all_append] using
        Bool.and_eq_true_iff.mpr ⟨maximumGuard_linear i j k, ih⟩

theorem literalFrameLinearity : MaximalPlainBranchTargets.LiteralFrameLinearity := by
  intro i p
  simpa only [frame, LinearRows.isLinear, LinearRows.atoms, List.all_append] using
    Bool.and_eq_true_iff.mpr ⟨lowerGuard_linear i (cutoff p) i, maxima_linear i i p.variables⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProof
