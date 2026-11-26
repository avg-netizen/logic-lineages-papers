module
public import LogicLineages.StandardControlCurrent.InactiveEliminationTargets
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceRosterProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InactiveEliminationCleaningProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm InactiveElimination

theorem clean_sum (as : List (Int × Summand)) (ν : Nat → Nat) :
    ((as.filter (fun a => a.1 != 0)).map (fun a => a.1 * (a.2.term.value ν : Int))).sum =
      (as.map (fun a => a.1 * (a.2.term.value ν : Int))).sum := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      by_cases h : a.1 = 0
      · simp [h, ih]
      · simp [h, ih]

theorem clean_row_value (r : Row) (ν : Nat → Nat) :
    rowValue (cleanRow r) ν = rowValue r ν := by
  simp only [rowValue,cleanRow,clean_sum]

theorem clean_atom_eval (a : Atom) (ν : Nat → Nat) :
    (cleanAtom a).eval ν ↔ a.eval ν := by
  cases a <;> simp only [cleanAtom,Atom.eval,clean_row_value]

theorem clean_eval (p : Formula) (ν : Nat → Nat) :
    (clean p).eval ν ↔ p.eval ν := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | atom a => exact clean_atom_eval a ν
  | negative p ih => exact not_congr ih
  | conjunction p q hp hq => exact and_congr hp hq
  | disjunction p q hp hq => exact or_congr hp hq

theorem clean_row_support (r : Row) (j : Nat) :
    j ∈ rowVariables (cleanRow r) → j ∈ rowVariables r := by
  intro h
  obtain ⟨a, ha, he⟩ := List.mem_map.mp h
  exact List.mem_map.mpr ⟨a,(List.mem_filter.mp ha).1,he⟩
theorem clean_support (p : Formula) (j : Nat) :
    j ∈ (clean p).variables → j ∈ p.variables := by
  induction p with
  | truth => exact id
  | falsity => exact id
  | atom a => cases a <;> exact clean_row_support _ j
  | negative p ih => exact ih
  | conjunction p q hp hq =>
      simp only [clean,Formula.variables,List.mem_append]
      exact Or.imp hp hq
  | disjunction p q hp hq =>
      simp only [clean,Formula.variables,List.mem_append]
      exact Or.imp hp hq

theorem inactive_row (xs : List Nat) (p : Formula) (i : Nat)
    (hi : i ∈ OrderedOccurrence.inactive xs p) (r : Row)
    (hr : r ∈ OrderedOccurrence.rows p) : LinearRows.rowLinear i (cleanRow r) = true := by
  rw [LinearRows.rowLinear,List.all_eq_true]
  intro a ha
  obtain ⟨ha,hc⟩ := List.mem_filter.mp ha
  have hc : a.1 ≠ 0 := by simpa only [bne_iff_ne] using hc
  obtain ⟨ri,hri⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨ai,hai⟩ := List.mem_iff_getElem?.mp ha
  have ho := (OrderedOccurrenceProof.exactRoster p ri ai a.1 a.2).mpr ⟨r,hri,hai⟩
  obtain ⟨hix,hnot⟩ := (OrderedOccurrenceProof.exactInactive xs p i).mp hi
  have hn (hh : OrderedOccurrence.nonlinear a.2 = true) : a.2.name ≠ i := by
    intro he
    have hl := (OrderedOccurrenceProof.exactLive xs p (ri,ai,a.1,a.2)).mpr
      ⟨ho,hc,hh,by simpa only [OrderedOccurrence.summand,he] using hix⟩
    exact hnot _ hl he
  cases hs : a.2 with
  | «variable» j => rfl
  | phi j e =>
      have h := hn (by simp [hs,OrderedOccurrence.nonlinear])
      simpa [hs,LinearRows.summandLinear,Summand.name] using h
  | hyperPhi j e h =>
      have h := hn (by simp [hs,OrderedOccurrence.nonlinear])
      simpa [hs,LinearRows.summandLinear,Summand.name] using h

theorem rows_clean (p : Formula) :
    LinearRows.atoms (clean p) = (LinearRows.atoms p).map cleanAtom := by
  induction p <;> simp_all [clean,LinearRows.atoms]

theorem atom_row_member (p : Formula) (a : Atom) (ha : a ∈ LinearRows.atoms p) :
    a.row ∈ OrderedOccurrence.rows p := by
  induction p with
  | truth => simpa [LinearRows.atoms] using ha
  | falsity => simpa [LinearRows.atoms] using ha
  | atom b =>
      have he : a = b := List.mem_singleton.mp ha
      subst a
      exact List.mem_singleton.mpr rfl
  | negative p ih => exact ih ha
  | conjunction p q hp hq =>
      rcases List.mem_append.mp ha with ha | ha
      · exact List.mem_append_left _ (hp ha)
      · exact List.mem_append_right _ (hq ha)
  | disjunction p q hp hq =>
      rcases List.mem_append.mp ha with ha | ha
      · exact List.mem_append_left _ (hp ha)
      · exact List.mem_append_right _ (hq ha)

theorem inactive_linear (xs : List Nat) (p : Formula) (i : Nat)
    (hi : i ∈ OrderedOccurrence.inactive xs p) : LinearRows.isLinear i (clean p) = true := by
  rw [LinearRows.isLinear,rows_clean,List.all_eq_true]
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  have h := inactive_row xs p i hi b.row (atom_row_member p b hb)
  cases b <;> exact h

theorem cleaning : InactiveEliminationTargets.Cleaning :=
  ⟨clean_eval,clean_support,inactive_linear⟩
end LogicLineages.StandardControlCurrent.InactiveEliminationCleaningProof
