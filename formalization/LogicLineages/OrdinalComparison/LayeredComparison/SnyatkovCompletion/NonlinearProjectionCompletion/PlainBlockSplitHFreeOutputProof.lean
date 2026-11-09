module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitOutputProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitHFreeBranchProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
open BlockRows PlainBlockSplit

theorem hfree_weighted_term (sign : Int → Nat) (entries : List (Int × NormalForm.Summand))
    (he : ∀ a ∈ entries, summandHFree a.2 = true) :
    termHFree (entries.foldr (fun a rest => Term.add (.multiply (sign a.1) a.2.term) rest)
      (.numeral 0)) = true := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    apply hfree_add
    · exact hfree_summand_term a.2 (he a List.mem_cons_self)
    · exact ih (fun b hb => he b (List.mem_cons_of_mem a hb))

theorem hfree_positive_term (r : Row) (hr : rowHFree r = true) :
    termHFree (positiveTerm r) = true := by
  have h := hfree_row_parts r hr
  exact hfree_add _ _ h.1 (hfree_weighted_term Int.toNat r.2 h.2.2)

theorem hfree_negative_term (r : Row) (hr : rowHFree r = true) :
    termHFree (negativeTerm r) = true := by
  have h := hfree_row_parts r hr
  exact hfree_add _ _ h.2.1 (hfree_weighted_term (fun c => (-c).toNat) r.2 h.2.2)

theorem hfree_compile_atom (a : Atom) (ha : rowHFree a.row = true) :
    matrixHFree a.compile = true := by
  have hp := hfree_positive_term a.row ha
  have hn := hfree_negative_term a.row ha
  cases a with
  | nonnegative r =>
    simp only [Atom.compile, atMost, matrixHFree, hp, hn, Bool.true_and]
  | divisible m r =>
    simp only [Atom.compile, absoluteTerm, matrixHFree, termHFree, hp, hn, Bool.true_and]

theorem hfree_compile_formula (p : Formula) (hp : formulaHFree p = true) :
    matrixHFree p.compile = true := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => exact hfree_compile_atom a hp
  | negative p ih => exact ih hp
  | conjunction p q ihp ihq =>
    have h := Bool.and_eq_true_iff.mp hp
    exact (Bool.and_eq_true_iff (x := matrixHFree p.compile)
      (y := matrixHFree q.compile)).mpr ⟨ihp h.1, ihq h.2⟩
  | disjunction p q ihp ihq =>
    have h := Bool.and_eq_true_iff.mp hp
    exact (Bool.and_eq_true_iff (x := matrixHFree p.compile)
      (y := matrixHFree q.compile)).mpr ⟨ihp h.1, ihq h.2⟩

theorem hfree_matrix_any (ps : List Matrix) (hp : ∀ p ∈ ps, matrixHFree p = true) :
    matrixHFree (Matrix.any ps) = true := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    exact (Bool.and_eq_true_iff (x := matrixHFree p) (y := matrixHFree (Matrix.any ps))).mpr
      ⟨hp p List.mem_cons_self, ih (fun q hq => hp q (List.mem_cons_of_mem p hq))⟩

theorem advance_hfree (states : List State) (hgood : GoodFrontier states)
    (hh : ∀ s ∈ states, formulaHFree s.2 = true) :
    ∀ s ∈ advance states, formulaHFree s.2 = true := by
  intro q hq
  obtain ⟨s, hs, hcase⟩ := (mem_advance states q).mp hq
  rcases hcase with ⟨_, rfl⟩ | ⟨_, hbranch⟩
  · exact hh s hs
  · have hg := hgood s hs
    exact hFreeBranchClosure s.1 s.2 hg.2.1 hg.2.2 (hh s hs) q hbranch

theorem run_hfree (fuel : Nat) (states : List State) (hgood : GoodFrontier states)
    (hh : ∀ s ∈ states, formulaHFree s.2 = true) :
    ∀ s ∈ run fuel states, formulaHFree s.2 = true := by
  induction fuel generalizing states with
  | zero => exact hh
  | succ fuel ih =>
    rw [run_succ]
    exact ih (advance states) (advance_good states hgood) (advance_hfree states hgood hh)

/-- The actual fixed-length uniform projector emits Phi/inverse arithmetic
only, so it can be graph-expanded for the next original source quantifier. -/
theorem hFreeOutputClosure : PlainBlockSplitTargets.HFreeOutputClosure := by
  intro bound p hnd ha hp hh
  apply hfree_matrix_any
  intro m hm
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
  apply hfree_compile_formula
  apply run_hfree bound.length [(bound, p)] (initial_good bound p hnd ha hp) _ s hs
  intro q hq
  have he : q = (bound, p) := List.mem_singleton.mp hq
  simpa only [he] using hh

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitProof
