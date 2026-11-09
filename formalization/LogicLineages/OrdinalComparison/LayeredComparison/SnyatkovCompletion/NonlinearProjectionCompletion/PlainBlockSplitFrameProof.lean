module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitBasicProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumStatementChecks
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainMaximumResidueStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
open BlockRows PlainBlockSplit

theorem all_eval (ps : List Formula) (ν : Nat → Nat) :
    (all ps).eval ν ↔ ∀ p ∈ ps, p.eval ν := by
  induction ps with
  | nil => simp [all, Formula.eval]
  | cons p ps ih =>
    simp only [all, Formula.eval, ih, List.mem_cons, forall_eq_or_imp]

theorem lower_guard_eval (i c : Nat) (ν : Nat → Nat) :
    (lowerGuard i c).eval ν ↔ c ≤ ν i := by
  simp only [lowerGuard, Formula.eval, Atom.eval, rowValue, Term.value,
    NormalForm.Summand.term, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    one_mul, add_zero]
  omega

theorem strict_maximum_guard_eval (i j : Nat) (ν : Nat → Nat) :
    (strictMaximumGuard i j).eval ν ↔ ν j < ν i := by
  simp only [strictMaximumGuard, Formula.eval, Atom.eval, rowValue, Term.value,
    NormalForm.Summand.term, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    one_mul, neg_one_mul, add_zero]
  omega

theorem frame_eval (bound : List Nat) (i : Nat) (p : Formula) (ν : Nat → Nat) :
    (frame bound i p).eval ν ↔
      cutoff p ≤ ν i ∧ ∀ j ∈ bound, j ≠ i → ν j < ν i := by
  constructor
  · rintro ⟨hlo, hmax⟩
    refine ⟨(lower_guard_eval i (cutoff p) ν).mp hlo, ?_⟩
    intro j hj hne
    apply (strict_maximum_guard_eval i j ν).mp
    apply (all_eval _ ν).mp hmax
    exact List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨hj, by simpa using hne⟩, rfl⟩
  · rintro ⟨hlo, hmax⟩
    refine ⟨(lower_guard_eval i (cutoff p) ν).mpr hlo, (all_eval _ ν).mpr ?_⟩
    intro q hq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    obtain ⟨hj, hne⟩ := List.mem_filter.mp hj
    exact (strict_maximum_guard_eval i j ν).mpr (hmax j hj (by simpa using hne))

theorem outside_row_eval (i : Nat) (r : Row) (ν : Nat → Nat) :
    (outsideRow i r).eval ν ↔ PlainMaximum.OutsideBoundary i r ν := by
  by_cases ha : PlainMaximum.headCoefficient i r = 0
  · simp [outsideRow, PlainMaximum.OutsideBoundary, ha, Formula.eval]
  · unfold PlainMaximum.OutsideBoundary
    simp only [ha, false_or]
    simp only [outsideRow, if_neg ha, Formula.eval, Atom.eval, rowValue, Term.value,
      NormalForm.Summand.term, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      one_mul, neg_one_mul, add_zero, Int.natCast_add]
    omega

theorem outside_nonnegative (i : Nat) (p : Formula) (r : Row) (ν : Nat → Nat)
    (hout : (outside i p).eval ν) (hr : Atom.nonnegative r ∈ atoms p) :
    PlainMaximum.OutsideBoundary i r ν := by
  apply (outside_row_eval i r ν).mp
  apply (all_eval _ ν).mp hout
  exact List.mem_map.mpr ⟨.nonnegative r, hr, rfl⟩

private theorem sum_member_le (xs : List Nat) (n : Nat) (hn : n ∈ xs) : n ≤ xs.sum := by
  induction xs with
  | nil => simp at hn
  | cons a xs ih =>
    rcases List.mem_cons.mp hn with h | h
    · subst n
      simp only [List.sum_cons]
      omega
    · have hh := ih h
      simp only [List.sum_cons]
      omega

theorem charge_le (p : Formula) (a : Atom) (ha : a ∈ atoms p) :
    atomCharge a ≤ ((atoms p).map atomCharge).sum :=
  sum_member_le _ _ (List.mem_map.mpr ⟨a, ha, rfl⟩)

theorem row_cutoff_le (p : Formula) (a : Atom) (ha : a ∈ atoms p) :
    PlainMaximum.cutoff a.row ≤ cutoff p := by
  have h := charge_le p a ha
  have hmass : 4 * PlainMaximum.mass a.row ≤ atomCharge a := by
    cases a <;> simp only [atomCharge, Atom.row] <;> omega
  unfold PlainMaximum.cutoff cutoff
  omega

theorem residue_cutoff_le (p : Formula) (m : Nat) (r : Row)
    (ha : Atom.divisible m r ∈ atoms p) : PlainMaximumResidue.cutoff m ≤ cutoff p := by
  have h := charge_le p (.divisible m r) ha
  simp only [atomCharge, Atom.row] at h
  unfold PlainMaximumResidue.cutoff cutoff
  omega

theorem allowed_atoms_iff (bound : List Nat) (p : Formula) :
    TiedLinear.allowed bound p = true ↔
      ∀ a ∈ atoms p, PlainMaximum.allowed bound a.row = true := by
  induction p with
  | truth => simp [TiedLinear.allowed, atoms]
  | falsity => simp [TiedLinear.allowed, atoms]
  | atom a => simp [TiedLinear.allowed, atoms]
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
    simp only [TiedLinear.allowed, Bool.and_eq_true, ihp, ihq, atoms,
      List.mem_append, or_imp, forall_and]
  | disjunction p q ihp ihq =>
    simp only [TiedLinear.allowed, Bool.and_eq_true, ihp, ihq, atoms,
      List.mem_append, or_imp, forall_and]

theorem atom_parameter_support (p : Formula) (a : Atom) (ha : a ∈ atoms p)
    (j : Nat) (hj : j ∈ a.row.parameters) : j ∈ p.parameters := by
  induction p with
  | truth => simp [atoms] at ha
  | falsity => simp [atoms] at ha
  | atom b =>
    have he : a = b := List.mem_singleton.mp ha
    subst a
    exact hj
  | negative p ih => exact ih ha
  | conjunction p q ihp ihq =>
    rcases List.mem_append.mp ha with h | h
    · exact List.mem_append_left _ (ihp h)
    · exact List.mem_append_right _ (ihq h)
  | disjunction p q ihp ihq =>
    rcases List.mem_append.mp ha with h | h
    · exact List.mem_append_left _ (ihp h)
    · exact List.mem_append_right _ (ihq h)

private theorem linearize_truth_congr (i : Nat) (p : Formula) (ν : Nat → Nat)
    (hatoms : ∀ a ∈ atoms p, (linearize i (.atom a)).eval ν ↔ a.eval ν) :
    (linearize i p).eval ν ↔ p.eval ν := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => exact hatoms a List.mem_cons_self
  | negative p ih => exact not_congr (ih hatoms)
  | conjunction p q ihp ihq =>
    exact and_congr
      (ihp (fun a ha => hatoms a (List.mem_append_left _ ha)))
      (ihq (fun a ha => hatoms a (List.mem_append_right _ ha)))
  | disjunction p q ihp ihq =>
    exact or_congr
      (ihp (fun a ha => hatoms a (List.mem_append_left _ ha)))
      (ihq (fun a ha => hatoms a (List.mem_append_right _ ha)))

/-- Actual nonlinear-to-linear truth for the original WHOLE Boolean matrix
under the computed unique-maximum, literal cutoff and all-row outside guards.
Both atom clauses are paid by the sealed original-data scalar packets. -/
theorem linearize_under_frame (bound : List Nat) (p : Formula) (i : Nat)
    (ν : Nat → Nat) (hi : i ∈ bound) (hallowed : TiedLinear.allowed bound p = true)
    (hparams : ParametersIndependent bound p)
    (hframe : (frame bound i p).eval ν) (hout : (outside i p).eval ν) :
    (linearize i p).eval ν ↔ p.eval ν := by
  obtain ⟨hcut, hmax⟩ := (frame_eval bound i p ν).mp hframe
  have hUnique : PlainMaximum.UniqueMaximum bound i ν := ⟨hi, hmax⟩
  apply linearize_truth_congr
  intro a ha
  have hrow := (allowed_atoms_iff bound p).mp hallowed a ha
  have hrowparams : ∀ j ∈ bound, j ∉ a.row.parameters := by
    intro j hj hparam
    exact hparams j hj (atom_parameter_support p a ha j hparam)
  cases a with
  | nonnegative r =>
    exact PlainMaximumProof.actualNonnegativeLinearization bound r i ν hrow hrowparams
      hUnique ((row_cutoff_le p (.nonnegative r) ha).trans hcut)
      (outside_nonnegative i p r ν hout ha)
  | divisible m r =>
    exact PlainMaximumResidueProof.actualOriginalTailCalibration m i r ν
      ((residue_cutoff_le p m r ha).trans hcut)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
