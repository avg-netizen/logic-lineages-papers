module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphProof
open ExpandedBooleanGraph NormalForm

theorem literalForestSupport : ExpandedBooleanGraphTargets.LiteralForestSupport := by
  intro p
  induction p <;> simp_all only [forest, Term.variables, Matrix.variables]

theorem hFreeOriginalForest : ExpandedBooleanGraphTargets.HFreeOriginalForest := by
  intro p
  induction p <;> simp_all only [forest, PlainBlockSplit.termHFree,
    PlainBlockSplit.matrixHFree, Bool.and_eq_true_iff, and_self, implies_true]

theorem mem_le_foldr_max (xs : List Nat) (i : Nat) (hi : i ∈ xs) :
    i ≤ xs.foldr max 0 := by
  induction xs with
  | nil => exact False.elim (List.not_mem_nil hi)
  | cons j xs ih =>
      rcases List.mem_cons.mp hi with rfl | hi
      · exact le_max_left _ _
      · exact le_trans (ih hi) (le_max_right _ _)

theorem original_name_lt_start (bound : List Nat) (p : Matrix) (i : Nat)
    (hi : i ∈ bound ∨ i ∈ p.variables) : i < startFor bound p := by
  have h := mem_le_foldr_max (bound ++ p.variables) i (List.mem_append.mpr hi)
  unfold startFor
  omega

theorem start_fresh (bound : List Nat) (p : Matrix) :
    ExpandedGraph.Fresh (startFor bound p) (forest p) := by
  intro i hi
  rw [literalForestSupport] at hi
  exact original_name_lt_start bound p i (Or.inr hi)

theorem exactFreshGraphNames : ExpandedBooleanGraphTargets.ExactFreshGraphNames := by
  intro bound p
  refine ⟨(ExpandedGraphProof.exactAllocation (startFor bound p) (forest p)).2.1, ?_⟩
  intro i hi
  have hlow := (ExpandedGraphProof.mem_allocated (startFor bound p) (forest p) i).mp hi
  constructor
  · intro hb
    have hhigh := original_name_lt_start bound p i (Or.inl hb)
    omega
  · intro hp
    have hhigh := original_name_lt_start bound p i (Or.inr hp)
    omega

theorem matrix_eval_congr (p : Matrix) (ν σ : Nat → Nat)
    (h : ∀ i ∈ p.variables, ν i = σ i) : p.eval ν ↔ p.eval σ := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | equal a b =>
      have ha := ExpandedGraphProof.term_value_congr a ν σ (fun i hi => h i (List.mem_append_left _ hi))
      have hb := ExpandedGraphProof.term_value_congr b ν σ (fun i hi => h i (List.mem_append_right _ hi))
      simp only [Matrix.eval, ha, hb]
  | less a b =>
      have ha := ExpandedGraphProof.term_value_congr a ν σ (fun i hi => h i (List.mem_append_left _ hi))
      have hb := ExpandedGraphProof.term_value_congr b ν σ (fun i hi => h i (List.mem_append_right _ hi))
      simp only [Matrix.eval, ha, hb]
  | divisible m a =>
      have ha := ExpandedGraphProof.term_value_congr a ν σ h
      simp only [Matrix.eval, ha]
  | negative p ih => exact not_congr (ih h)
  | conjunction p q ihp ihq =>
      exact and_congr (ihp (fun i hi => h i (List.mem_append_left _ hi)))
        (ihq (fun i hi => h i (List.mem_append_right _ hi)))
  | disjunction p q ihp ihq =>
      exact or_congr (ihp (fun i hi => h i (List.mem_append_left _ hi)))
        (ihq (fun i hi => h i (List.mem_append_right _ hi)))

#print axioms literalForestSupport
#print axioms hFreeOriginalForest
#print axioms mem_le_foldr_max
#print axioms original_name_lt_start
#print axioms start_fresh
#print axioms exactFreshGraphNames
#print axioms matrix_eval_congr
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphProof
