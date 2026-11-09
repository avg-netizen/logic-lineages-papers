module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitFrontierProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
open BlockRows PlainBlockSplit

/-- Compilation preserves literal original names even in zero-weight terms. -/
theorem weighted_term_support (sign : Int → Nat) (entries : List (Int × NormalForm.Summand))
    (j : Nat) (hj : j ∈ (entries.foldr (fun a rest =>
      Term.add (.multiply (sign a.1) a.2.term) rest) (.numeral 0)).variables) :
    j ∈ entries.map (fun a => a.2.name) := by
  induction entries with
  | nil => simp [Term.variables] at hj
  | cons a entries ih =>
    rcases List.mem_append.mp hj with hhead | htail
    · have he : j = a.2.name := (BlockRowsProof.original_summand_variables a.2 j).mp hhead
      exact List.mem_cons.mpr (Or.inl he)
    · exact List.mem_cons.mpr (Or.inr (ih htail))

theorem positive_term_support (r : Row) (j : Nat) (hj : j ∈ (positiveTerm r).variables) :
    j ∈ r.variables := by
  rcases List.mem_append.mp hj with hp | ho
  · exact List.mem_append_left _ (List.mem_append_left _ hp)
  · exact List.mem_append_right _ (weighted_term_support Int.toNat r.2 j ho)

theorem negative_term_support (r : Row) (j : Nat) (hj : j ∈ (negativeTerm r).variables) :
    j ∈ r.variables := by
  rcases List.mem_append.mp hj with hn | ho
  · exact List.mem_append_left _ (List.mem_append_right _ hn)
  · exact List.mem_append_right _ (weighted_term_support (fun c => (-c).toNat) r.2 j ho)

theorem atom_compile_support (a : Atom) (j : Nat) (hj : j ∈ a.compile.variables) :
    j ∈ a.row.variables := by
  cases a with
  | nonnegative r =>
    change j ∈ (positiveTerm r).variables ++ (negativeTerm r).variables at hj
    rcases List.mem_append.mp hj with h | h
    · exact positive_term_support r j h
    · exact negative_term_support r j h
  | divisible m r =>
    change j ∈ ((positiveTerm r).variables ++ (negativeTerm r).variables) ++
      ((negativeTerm r).variables ++ (positiveTerm r).variables) at hj
    rcases List.mem_append.mp hj with h | h
    · rcases List.mem_append.mp h with h | h
      · exact positive_term_support r j h
      · exact negative_term_support r j h
    · rcases List.mem_append.mp h with h | h
      · exact negative_term_support r j h
      · exact positive_term_support r j h

theorem formula_compile_support (p : Formula) (j : Nat) (hj : j ∈ p.compile.variables) :
    j ∈ p.variables := by
  induction p with
  | truth => exact False.elim (List.not_mem_nil hj)
  | falsity => exact False.elim (List.not_mem_nil hj)
  | atom a => exact atom_compile_support a j hj
  | negative p ih => exact ih hj
  | conjunction p q ihp ihq =>
    rcases List.mem_append.mp hj with h | h
    · exact List.mem_append_left _ (ihp h)
    · exact List.mem_append_right _ (ihq h)
  | disjunction p q ihp ihq =>
    rcases List.mem_append.mp hj with h | h
    · exact List.mem_append_left _ (ihp h)
    · exact List.mem_append_right _ (ihq h)

theorem finished_variables_are_parameters (p : Formula) (ha : TiedLinear.allowed [] p = true)
    (j : Nat) (hj : j ∈ p.variables) : j ∈ p.parameters := by
  rcases variable_cases p j hj with hp | ⟨a, hmem, he⟩
  · exact hp
  · have hclass := (TiedLinearProof.allowed_formula_iff [] p).mp ha a hmem
    exact False.elim (List.not_mem_nil (allowed_summand_name [] a.2 hclass))

/-- No erased original name can reenter through a later parameter constant:
parameter support is traced through every concrete predecessor branch. -/
theorem originalOutputNameSupport : PlainBlockSplitTargets.OriginalOutputNameSupport := by
  intro bound p hnd ha hp j hj
  rw [project, WindowProof.any_support] at hj
  obtain ⟨m, hm, hjm⟩ := hj
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
  have hfinish : s.1 = [] := by
    apply run_finishes bound.length [(bound, p)] _ s hs
    intro q hq
    have he : q = (bound, p) := List.mem_singleton.mp hq
    subst q
    exact le_rfl
  have hg := run_good bound.length [(bound, p)] (initial_good bound p hnd ha hp) s hs
  have hallowed : TiedLinear.allowed [] s.2 = true := by simpa only [hfinish] using hg.2.1
  have hjparam := finished_variables_are_parameters s.2 hallowed j (formula_compile_support s.2 j hjm)
  obtain ⟨q, hq, hjq⟩ := run_parameter_support bound.length [(bound, p)] s hs j hjparam
  have he : q = (bound, p) := List.mem_singleton.mp hq
  have hjp : j ∈ p.parameters := by simpa only [he] using hjq
  exact ⟨fun hbound => hp j hbound hjp, parameters_in_variables p j hjp⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
