module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitHFreeCoreProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
open BlockRows PlainBlockSplit

theorem hfree_conjunction (p q : Formula) (hp : formulaHFree p = true) (hq : formulaHFree q = true) :
    formulaHFree (.conjunction p q) = true :=
  (Bool.and_eq_true_iff (x := formulaHFree p) (y := formulaHFree q)).mpr ⟨hp, hq⟩

theorem hfree_substitute_entries (i : Nat) (t positive negative : Term)
    (entries : List (Int × NormalForm.Summand))
    (ht : termHFree t = true) (hp : termHFree positive = true) (hn : termHFree negative = true)
    (he : ∀ a ∈ entries, summandHFree a.2 = true) :
    rowHFree (substituteEntries i t positive negative entries) = true := by
  induction entries with
  | nil => exact hfree_row_of_parts _ hp hn (by simp [substituteEntries])
  | cons a entries ih =>
    have htail := ih (fun b hb => he b (List.mem_cons_of_mem a hb))
    have hparts := hfree_row_parts _ htail
    by_cases hname : a.2.name = i
    · have hterm := hfree_term_substitution a.2.term i t
        (hfree_summand_term a.2 (he a List.mem_cons_self)) ht
      simp only [substituteEntries, if_pos hname]
      apply hfree_row_of_parts
      · exact hfree_add _ _ hterm hparts.1
      · exact hfree_add _ _ hterm hparts.2.1
      · exact hparts.2.2
    · simp only [substituteEntries, if_neg hname]
      apply hfree_row_of_parts
      · exact hparts.1
      · exact hparts.2.1
      · intro b hb
        rcases List.mem_cons.mp hb with hb | hb
        · subst b; exact he a List.mem_cons_self
        · exact hparts.2.2 b hb

theorem hfree_row_substitute (r : Row) (i : Nat) (t : Term)
    (hr : rowHFree r = true) (ht : termHFree t = true) : rowHFree (r.substitute i t) = true := by
  have h := hfree_row_parts r hr
  exact hfree_substitute_entries i t _ _ r.2 ht
    (hfree_term_substitution r.1.1 i t h.1 ht)
    (hfree_term_substitution r.1.2 i t h.2.1 ht) h.2.2

theorem hfree_formula_substitute (p : Formula) (i : Nat) (t : Term)
    (hp : formulaHFree p = true) (ht : termHFree t = true) :
    formulaHFree (p.substitute i t) = true := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => cases a <;> exact hfree_row_substitute _ i t hp ht
  | negative p ih => exact ih hp
  | conjunction p q ihp ihq =>
    have h := Bool.and_eq_true_iff.mp hp
    exact hfree_conjunction _ _ (ihp h.1) (ihq h.2)
  | disjunction p q ihp ihq =>
    have h := Bool.and_eq_true_iff.mp hp
    exact (Bool.and_eq_true_iff (x := formulaHFree (p.substitute i t))
      (y := formulaHFree (q.substitute i t))).mpr ⟨ihp h.1, ihq h.2⟩

theorem hfree_rename_summand (i j : Nat) (s : NormalForm.Summand) :
    summandHFree (renameSummand i j s) = summandHFree s := by cases s <;> rfl

theorem hfree_rename_row (r : Row) (i j : Nat) (hr : rowHFree r = true) :
    rowHFree (renameRow i j r) = true := by
  have h := hfree_row_parts r hr
  apply hfree_row_of_parts _ h.1 h.2.1
  intro b hb
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
  rw [hfree_rename_summand]
  exact h.2.2 c hc

theorem hfree_rename (p : Formula) (i j : Nat) (hp : formulaHFree p = true) :
    formulaHFree (rename i j p) = true := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => cases a <;> exact hfree_rename_row _ i j hp
  | negative p ih => exact ih hp
  | conjunction p q ihp ihq =>
    have h := Bool.and_eq_true_iff.mp hp
    exact hfree_conjunction _ _ (ihp h.1) (ihq h.2)
  | disjunction p q ihp ihq =>
    have h := Bool.and_eq_true_iff.mp hp
    exact (Bool.and_eq_true_iff (x := formulaHFree (rename i j p))
      (y := formulaHFree (rename i j q))).mpr ⟨ihp h.1, ihq h.2⟩

theorem hfree_boundary (i : Nat) (r : Row) (hr : rowHFree r = true) :
    termHFree (PlainMaximum.boundary i r) = true := by
  have h := hfree_row_parts r hr
  simp only [PlainMaximum.boundary, DominantBoundary.center, PlainMaximum.absoluteConstant,
    termHFree, h.1, h.2.1, Bool.true_and]

theorem hfree_filtered_row (i : Nat) (r : Row) (hr : rowHFree r = true) :
    rowHFree (PlainMaximum.dropHead i r) = true := by
  have h := hfree_row_parts r hr
  apply hfree_row_of_parts _ h.1 h.2.1
  intro a ha
  exact h.2.2 a (List.mem_filter.mp ha).1

theorem hfree_nonnegative (i : Nat) (r : Row) (hr : rowHFree r = true) :
    formulaHFree (PlainMaximum.linearizeNonnegative i r) = true := by
  have h := hfree_row_parts r hr
  have hb := hfree_boundary i r hr
  by_cases hpos : 0 < PlainMaximum.headCoefficient i r
  · simp [PlainMaximum.linearizeNonnegative, hpos, PlainMaximum.positiveGuard,
      formulaHFree, rowHFree, Atom.row, termHFree, summandHFree, h.1, h.2.1, hb]
  · by_cases hneg : PlainMaximum.headCoefficient i r < 0
    · simp [PlainMaximum.linearizeNonnegative, hpos, hneg, PlainMaximum.negativeGuard,
        formulaHFree, rowHFree, Atom.row, termHFree, summandHFree, h.1, h.2.1, hb]
    · rw [PlainMaximum.linearizeNonnegative, if_neg hpos, if_neg hneg]
      exact hfree_filtered_row i r hr

theorem hfree_residue (m i : Nat) (r : Row) (hr : rowHFree r = true) :
    formulaHFree (PlainMaximumResidue.lowerAtom m i r) = true := by
  have h := hfree_row_parts r hr
  apply hfree_row_of_parts
  · exact hfree_add _ _ h.1 rfl
  · exact hfree_add _ _ h.2.1 rfl
  · intro a ha
    exact h.2.2 a (List.mem_filter.mp ha).1

theorem hfree_all (ps : List Formula) (hp : ∀ p ∈ ps, formulaHFree p = true) :
    formulaHFree (all ps) = true := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    exact hfree_conjunction p (all ps) (hp p List.mem_cons_self)
      (ih (fun q hq => hp q (List.mem_cons_of_mem p hq)))

theorem hfree_frame (bound : List Nat) (i : Nat) (p : Formula) :
    formulaHFree (frame bound i p) = true := by
  apply hfree_conjunction
  · rfl
  · apply hfree_all
    intro q hq
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hq
    rfl

theorem hfree_atom (p : Formula) (hp : formulaHFree p = true) (a : Atom) (ha : a ∈ atoms p) :
    rowHFree a.row = true := by
  induction p with
  | truth => exact False.elim (List.not_mem_nil ha)
  | falsity => exact False.elim (List.not_mem_nil ha)
  | atom b => have he := List.mem_singleton.mp ha; subst a; exact hp
  | negative p ih => exact ih hp ha
  | conjunction p q ihp ihq =>
    have h := Bool.and_eq_true_iff.mp hp
    rcases List.mem_append.mp ha with ha | ha
    · exact ihp h.1 ha
    · exact ihq h.2 ha
  | disjunction p q ihp ihq =>
    have h := Bool.and_eq_true_iff.mp hp
    rcases List.mem_append.mp ha with ha | ha
    · exact ihp h.1 ha
    · exact ihq h.2 ha

theorem hfree_outside_row (i : Nat) (r : Row) (hr : rowHFree r = true) :
    formulaHFree (outsideRow i r) = true := by
  have hb := hfree_boundary i r hr
  by_cases hz : PlainMaximum.headCoefficient i r = 0
  · simp [outsideRow, hz, formulaHFree]
  · simp [outsideRow, hz, formulaHFree, rowHFree, Atom.row, termHFree, summandHFree, hb]

theorem hfree_outside (i : Nat) (p : Formula) (hp : formulaHFree p = true) :
    formulaHFree (outside i p) = true := by
  apply hfree_all
  intro q hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  cases a with
  | nonnegative r => exact hfree_outside_row i r (hfree_atom p hp _ ha)
  | divisible m r => rfl

theorem hfree_linearize (i : Nat) (p : Formula) (hp : formulaHFree p = true) :
    formulaHFree (linearize i p) = true := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => cases a with
    | nonnegative r => exact hfree_nonnegative i r hp
    | divisible m r => exact hfree_residue m i r hp
  | negative p ih => exact ih hp
  | conjunction p q ihp ihq =>
    have h := Bool.and_eq_true_iff.mp hp
    exact hfree_conjunction _ _ (ihp h.1) (ihq h.2)
  | disjunction p q ihp ihq =>
    have h := Bool.and_eq_true_iff.mp hp
    exact (Bool.and_eq_true_iff (x := formulaHFree (linearize i p))
      (y := formulaHFree (linearize i q))).mpr ⟨ihp h.1, ihq h.2⟩

theorem hfree_actual_far (bound : List Nat) (i : Nat) (p : Formula) (hp : formulaHFree p = true) :
    formulaHFree (TiedLinear.eliminate i (.conjunction (frame bound i p)
      (.conjunction (outside i p) (linearize i p)))) = true :=
  hfree_tied_eliminate i _ (hfree_conjunction _ _ (hfree_frame bound i p)
    (hfree_conjunction _ _ (hfree_outside i p hp) (hfree_linearize i p hp)))

/-- Every literal branch of the source dispatcher remains in the Phi-only
expanded language; arbitrary old parameter terms keep their structure. -/
theorem hFreeBranchClosure : PlainBlockSplitTargets.HFreeBranchClosure := by
  intro bound p _ _ hp s hs
  change s ∈ ((small bound p ++ ties bound p) ++ bands bound p) ++ far bound p at hs
  rcases List.mem_append.mp hs with hleft | hfar
  · rcases List.mem_append.mp hleft with hleft | hbands
    · rcases List.mem_append.mp hleft with hsmall | hties
      · cases bound with
        | nil => exact False.elim (List.not_mem_nil hsmall)
        | cons i rest =>
          obtain ⟨n, _, rfl⟩ := List.mem_map.mp hsmall
          exact hfree_formula_substitute p i (.numeral n) hp rfl
      · obtain ⟨i, _, hinner⟩ := List.mem_flatMap.mp hties
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hinner
        exact hfree_rename p i j hp
    · obtain ⟨i, _, hinner⟩ := List.mem_flatMap.mp hbands
      obtain ⟨a, ha, hcase⟩ := List.mem_flatMap.mp hinner
      cases a with
      | nonnegative r =>
        change s ∈ (if PlainMaximum.headCoefficient i r = 0 then [] else
          (List.range 5).map (fun d => (bound.erase i, p.substitute i (bandCandidate i r d)))) at hcase
        by_cases hz : PlainMaximum.headCoefficient i r = 0
        · simp only [if_pos hz, List.not_mem_nil] at hcase
        · rw [if_neg hz] at hcase
          obtain ⟨d, _, rfl⟩ := List.mem_map.mp hcase
          apply hfree_formula_substitute p i _ hp
          exact hfree_add _ _ (hfree_subtract _ _ (hfree_boundary i r (hfree_atom p hp _ ha)) rfl) rfl
      | divisible m r => exact False.elim (List.not_mem_nil hcase)
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hfar
    exact hfree_actual_far bound i p hp

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
