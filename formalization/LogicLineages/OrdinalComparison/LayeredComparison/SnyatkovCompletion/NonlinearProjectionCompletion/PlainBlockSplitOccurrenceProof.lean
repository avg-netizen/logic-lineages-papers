module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitParameterProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
open BlockRows PlainBlockSplit

theorem allowed_summand_erase (bound : List Nat) (i : Nat) (s : NormalForm.Summand)
    (hs : PlainMaximum.allowedSummand bound s = true) (hne : s.name ≠ i) :
    PlainMaximum.allowedSummand (bound.erase i) s = true := by
  cases s with
  | «variable» j =>
    have hj : j ∈ bound := by simpa [PlainMaximum.allowedSummand] using hs
    have hji : j ≠ i := hne
    simpa [PlainMaximum.allowedSummand] using (List.mem_erase_of_ne hji).mpr hj
  | phi j shift =>
    have hj : j ∈ bound ∧ shift = 0 := by simpa [PlainMaximum.allowedSummand] using hs
    have hji : j ≠ i := hne
    simpa [PlainMaximum.allowedSummand] using
      And.intro ((List.mem_erase_of_ne hji).mpr hj.1) hj.2
  | hyperPhi j e h => simp [PlainMaximum.allowedSummand] at hs

theorem occurrences_substitute (p : Formula) (i : Nat) (t : Term) :
    PlainMaximum.occurrences (p.substitute i t) =
      (PlainMaximum.occurrences p).filter (fun a => a.2.name != i) := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => cases a <;> exact BlockRowsProof.exactRemainingOccurrences _ i t
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
    simp only [Formula.substitute, PlainMaximum.occurrences, ihp, ihq, List.filter_append]
  | disjunction p q ihp ihq =>
    simp only [Formula.substitute, PlainMaximum.occurrences, ihp, ihq, List.filter_append]

theorem allowed_substitute (bound : List Nat) (p : Formula) (i : Nat) (t : Term)
    (hp : TiedLinear.allowed bound p = true) :
    TiedLinear.allowed (bound.erase i) (p.substitute i t) = true := by
  apply (TiedLinearProof.allowed_formula_iff _ _).mpr
  intro a ha
  rw [occurrences_substitute] at ha
  obtain ⟨ha, hne⟩ := List.mem_filter.mp ha
  exact allowed_summand_erase bound i a.2
    ((TiedLinearProof.allowed_formula_iff bound p).mp hp a ha) (by simpa using hne)

theorem occurrences_rename (p : Formula) (i j : Nat) :
    PlainMaximum.occurrences (rename i j p) =
      (PlainMaximum.occurrences p).map (fun a => (a.1, renameSummand i j a.2)) := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => cases a <;> rfl
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
    simp only [rename, PlainMaximum.occurrences, ihp, ihq, List.map_append]
  | disjunction p q ihp ihq =>
    simp only [rename, PlainMaximum.occurrences, ihp, ihq, List.map_append]

theorem allowed_summand_rename (bound : List Nat) (i j : Nat) (s : NormalForm.Summand)
    (hs : PlainMaximum.allowedSummand bound s = true) (hj : j ∈ bound) (hji : j ≠ i) :
    PlainMaximum.allowedSummand (bound.erase i) (renameSummand i j s) = true := by
  have hjmem : j ∈ bound.erase i := (List.mem_erase_of_ne hji).mpr hj
  cases s with
  | «variable» k =>
    have hk : k ∈ bound := by simpa [PlainMaximum.allowedSummand] using hs
    by_cases hki : k = i
    · simpa [renameSummand, hki, PlainMaximum.allowedSummand] using hjmem
    · simpa [renameSummand, hki, PlainMaximum.allowedSummand] using (List.mem_erase_of_ne hki).mpr hk
  | phi k shift =>
    have hk : k ∈ bound ∧ shift = 0 := by simpa [PlainMaximum.allowedSummand] using hs
    by_cases hki : k = i
    · simpa [renameSummand, hki, PlainMaximum.allowedSummand] using And.intro hjmem hk.2
    · simpa [renameSummand, hki, PlainMaximum.allowedSummand] using
        And.intro ((List.mem_erase_of_ne hki).mpr hk.1) hk.2
  | hyperPhi k e h => simp [PlainMaximum.allowedSummand] at hs

theorem allowed_rename (bound : List Nat) (p : Formula) (i j : Nat)
    (hp : TiedLinear.allowed bound p = true) (hj : j ∈ bound) (hji : j ≠ i) :
    TiedLinear.allowed (bound.erase i) (rename i j p) = true := by
  apply (TiedLinearProof.allowed_formula_iff _ _).mpr
  intro a ha
  rw [occurrences_rename] at ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact allowed_summand_rename bound i j b.2
    ((TiedLinearProof.allowed_formula_iff bound p).mp hp b hb) hj hji

theorem allowed_conjunction (bound : List Nat) (p q : Formula)
    (hp : TiedLinear.allowed bound p = true) (hq : TiedLinear.allowed bound q = true) :
    TiedLinear.allowed bound (.conjunction p q) = true :=
  (Bool.and_eq_true_iff (x := TiedLinear.allowed bound p) (y := TiedLinear.allowed bound q)).mpr ⟨hp, hq⟩

theorem allowed_all (bound : List Nat) (ps : List Formula)
    (hps : ∀ p ∈ ps, TiedLinear.allowed bound p = true) : TiedLinear.allowed bound (all ps) = true := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    exact allowed_conjunction bound p (all ps) (hps p List.mem_cons_self)
      (ih (fun q hq => hps q (List.mem_cons_of_mem _ hq)))

theorem lower_guard_allowed (bound : List Nat) (i c : Nat) (hi : i ∈ bound) :
    TiedLinear.allowed bound (lowerGuard i c) = true := by
  simpa [lowerGuard, TiedLinear.allowed, PlainMaximum.allowed, Atom.row, PlainMaximum.allowedSummand] using hi

theorem strict_guard_allowed (bound : List Nat) (i j : Nat) (hi : i ∈ bound) (hj : j ∈ bound) :
    TiedLinear.allowed bound (strictMaximumGuard i j) = true := by
  simpa [strictMaximumGuard, TiedLinear.allowed, PlainMaximum.allowed, Atom.row,
    PlainMaximum.allowedSummand] using And.intro hi hj

theorem frame_allowed (bound : List Nat) (p : Formula) (i : Nat) (hi : i ∈ bound) :
    TiedLinear.allowed bound (frame bound i p) = true := by
  apply allowed_conjunction
  · exact lower_guard_allowed bound i (cutoff p) hi
  · apply allowed_all
    intro q hq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    exact strict_guard_allowed bound i j hi (List.mem_filter.mp hj).1

theorem outside_row_allowed (bound : List Nat) (i : Nat) (r : Row) (hi : i ∈ bound) :
    TiedLinear.allowed bound (outsideRow i r) = true := by
  by_cases hz : PlainMaximum.headCoefficient i r = 0 <;>
    simp [outsideRow, hz, TiedLinear.allowed, PlainMaximum.allowed, Atom.row,
      PlainMaximum.allowedSummand, hi]

theorem outside_allowed (bound : List Nat) (p : Formula) (i : Nat) (hi : i ∈ bound) :
    TiedLinear.allowed bound (outside i p) = true := by
  apply allowed_all
  intro q hq
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hq
  cases a with
  | nonnegative r => exact outside_row_allowed bound i r hi
  | divisible m r => rfl

private theorem filter_allowed (bound : List Nat) (r : Row) (i : Nat)
    (hallowed : PlainMaximum.allowed bound r = true) :
    (PlainMaximum.remainingOccurrences i r).all (fun a => PlainMaximum.allowedSummand bound a.2) = true := by
  apply List.all_eq_true.mpr
  intro a ha
  exact List.all_eq_true.mp hallowed a (List.mem_filter.mp ha).1

theorem nonnegative_allowed (bound : List Nat) (r : Row) (i : Nat)
    (hi : i ∈ bound) (hallowed : PlainMaximum.allowed bound r = true) :
    TiedLinear.allowed bound (PlainMaximum.linearizeNonnegative i r) = true := by
  by_cases ha : 0 < PlainMaximum.headCoefficient i r
  · simp [PlainMaximum.linearizeNonnegative, ha, PlainMaximum.positiveGuard,
      TiedLinear.allowed, PlainMaximum.allowed, Atom.row, PlainMaximum.allowedSummand, hi]
  · by_cases hb : PlainMaximum.headCoefficient i r < 0
    · simp [PlainMaximum.linearizeNonnegative, ha, hb, PlainMaximum.negativeGuard,
        TiedLinear.allowed, PlainMaximum.allowed, Atom.row, PlainMaximum.allowedSummand, hi]
    · rw [PlainMaximum.linearizeNonnegative, if_neg ha, if_neg hb]
      exact filter_allowed bound r i hallowed

theorem residue_allowed (bound : List Nat) (r : Row) (m i : Nat)
    (hallowed : PlainMaximum.allowed bound r = true) :
    TiedLinear.allowed bound (PlainMaximumResidue.lowerAtom m i r) = true :=
  filter_allowed bound r i hallowed

theorem linearize_allowed (bound : List Nat) (p : Formula) (i : Nat) (hi : i ∈ bound)
    (hallowed : TiedLinear.allowed bound p = true) : TiedLinear.allowed bound (linearize i p) = true := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a =>
    cases a with
    | nonnegative r => exact nonnegative_allowed bound r i hi hallowed
    | divisible m r => exact residue_allowed bound r m i hallowed
  | negative p ih => exact ih hallowed
  | conjunction p q ihp ihq =>
    obtain ⟨hap, haq⟩ := Bool.and_eq_true_iff.mp hallowed
    exact allowed_conjunction bound _ _ (ihp hap) (ihq haq)
  | disjunction p q ihp ihq =>
    obtain ⟨hap, haq⟩ := Bool.and_eq_true_iff.mp hallowed
    exact (Bool.and_eq_true_iff
      (x := TiedLinear.allowed bound (linearize i p))
      (y := TiedLinear.allowed bound (linearize i q))).mpr ⟨ihp hap, ihq haq⟩

theorem far_allowed (bound : List Nat) (p : Formula) (i : Nat) (hi : i ∈ bound)
    (hallowed : TiedLinear.allowed bound p = true) (hparams : ParametersIndependent bound p) :
    TiedLinear.allowed (bound.erase i) (TiedLinear.eliminate i
    (.conjunction (frame bound i p) (.conjunction (outside i p) (linearize i p)))) = true :=
  TiedLinearProof.remainingPlainClass bound i
    (.conjunction (frame bound i p) (.conjunction (outside i p) (linearize i p)))
    (allowed_conjunction bound _ _ (frame_allowed bound p i hi)
      (allowed_conjunction bound _ _ (outside_allowed bound p i hi) (linearize_allowed bound p i hi hallowed)))
    (far_input_linear bound p i hi hallowed hparams)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
