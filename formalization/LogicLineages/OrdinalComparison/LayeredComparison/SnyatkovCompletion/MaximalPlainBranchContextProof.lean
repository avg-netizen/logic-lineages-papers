module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchFrameProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainRowsSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProof
open NormalForm MaximalPlainBranch

private theorem sum_member_le (xs : List Nat) (n : Nat) (h : n ∈ xs) : n ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
      simp only [List.mem_cons] at h
      simp only [List.sum_cons]
      rcases h with rfl | h
      · omega
      · have := ih h; omega

theorem atom_cutoff_le (p : Formula) (a : Atom) (ha : a ∈ LinearRows.atoms p) :
    MaximalPlainRows.cutoff a ≤ cutoff p :=
  sum_member_le _ _ (List.mem_map.mpr ⟨a, ha, rfl⟩)

theorem variables_from_atoms (p : Formula) :
    p.variables = (LinearRows.atoms p).flatMap (fun a => rowVariables a.row) := by
  induction p <;> simp [Formula.variables, LinearRows.atoms, *]

theorem atom_name_mem (p : Formula) (a : Atom) (ha : a ∈ LinearRows.atoms p)
    (b : Int × Summand) (hb : b ∈ a.row.2) : b.2.name ∈ p.variables := by
  rw [variables_from_atoms]
  exact List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩

private theorem compile_eval (i : Nat) (p : Formula) (ν : Nat → Nat)
    (h : ∀ a ∈ LinearRows.atoms p, (MaximalPlainRows.compileAtom i a).eval ν ↔ a.eval ν) :
    (compile i p).eval ν ↔ p.eval ν := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => exact h a (by simp [LinearRows.atoms])
  | negative p ih => exact not_congr (ih h)
  | conjunction p q ihp ihq =>
      exact and_congr (ihp (fun a ha => h a (List.mem_append_left _ ha)))
        (ihq (fun a ha => h a (List.mem_append_right _ ha)))
  | disjunction p q ihp ihq =>
      exact or_congr (ihp (fun a ha => h a (List.mem_append_left _ ha)))
        (ihq (fun a ha => h a (List.mem_append_right _ ha)))

theorem actualContextualCompilation : MaximalPlainBranchTargets.ActualContextualCompilation := by
  intro i p hp ν hc hm
  apply compile_eval
  intro a ha
  have hplain := List.all_eq_true.mp hp a ha
  exact MaximalPlainRowsProof.actualMaximalTailAtom i a hplain ν
    (le_trans (atom_cutoff_le p a ha) hc)
    (fun b hb => hm b.2.name (atom_name_mem p a ha b hb))

private theorem compile_linear (i : Nat) (p : Formula)
    (h : ∀ a ∈ LinearRows.atoms p, PlainPhiDominance.isPlain a.row = true) :
    LinearRows.isLinear i (compile i p) = true := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => exact MaximalPlainRowsProof.literalTailLinearity i a (h a (by simp [LinearRows.atoms]))
  | negative p ih => exact ih h
  | conjunction p q ihp ihq =>
      have hp := ihp (fun a ha => h a (List.mem_append_left _ ha))
      have hq := ihq (fun a ha => h a (List.mem_append_right _ ha))
      simpa only [compile, LinearRows.isLinear, LinearRows.atoms, List.all_append] using
        Bool.and_eq_true_iff.mpr ⟨hp, hq⟩
  | disjunction p q ihp ihq =>
      have hp := ihp (fun a ha => h a (List.mem_append_left _ ha))
      have hq := ihq (fun a ha => h a (List.mem_append_right _ ha))
      simpa only [compile, LinearRows.isLinear, LinearRows.atoms, List.all_append] using
        Bool.and_eq_true_iff.mpr ⟨hp, hq⟩

theorem literalContextualLinearity : MaximalPlainBranchTargets.LiteralContextualLinearity := by
  intro i p hp
  have hc := compile_linear i p (List.all_eq_true.mp hp)
  simpa only [framed, LinearRows.isLinear, LinearRows.atoms, List.all_append] using
    Bool.and_eq_true_iff.mpr ⟨literalFrameLinearity i p, hc⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchProof
