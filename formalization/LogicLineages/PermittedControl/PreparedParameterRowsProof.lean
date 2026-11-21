module
public import LogicLineages.PermittedControl.PreparedParameterProjectionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open NormalForm LinearRows

def PlainPreparedRow (r : Row) : Prop :=
  ∀ s ∈ r.2, ∃ i : Nat, s.2 = .variable i

theorem prepared_const_plain (c : Int) : PlainPreparedRow (rowConst c) := by
  intro s hs
  simp [rowConst] at hs

theorem prepared_add_plain (r s : Row) (hr : PlainPreparedRow r) (hs : PlainPreparedRow s) :
    PlainPreparedRow (rowAdd r s) := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact hr a h
  · exact hs a h

theorem prepared_scale_plain (z : Int) (r : Row) (hr : PlainPreparedRow r) :
    PlainPreparedRow (rowScale z r) := by
  intro a ha
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ha
  exact hr s hs

private theorem prepared_remainder_plain (i : Nat) (r : Row) (hr : PlainPreparedRow r) :
    PlainPreparedRow (remainder i r) := by
  intro a ha
  exact hr a (List.mem_filter.mp ha).1

theorem prepared_adjust_atom_plain (i M : Nat) (a : Atom) (ha : PlainPreparedRow a.row) :
    PlainPreparedRow (adjustAtom i M a).row := by
  cases a with
  | nonnegative r =>
    simp only [adjustAtom]
    split
    · exact prepared_remainder_plain i r ha
    · exact prepared_scale_plain _ _ (prepared_remainder_plain i r ha)
  | divisible m r =>
    simp only [adjustAtom]
    split
    · exact prepared_remainder_plain i r ha
    · exact prepared_scale_plain _ _ (prepared_remainder_plain i r ha)

theorem prepared_instantiate_atom_plain (a : UnitAtom) (b : Row)
    (ha : PlainPreparedRow a.row) (hb : PlainPreparedRow b) :
    PlainPreparedRow (a.instantiate b).row := by
  cases a <;> exact prepared_add_plain _ _ (prepared_scale_plain _ _ hb) ha

theorem prepared_cutoff_atom_plain (a : UnitAtom) (b : Row) (ha : PlainPreparedRow a.row)
    (hb : b ∈ a.cutoffs) : PlainPreparedRow b := by
  cases a with
  | nonnegative s r =>
    cases s with
    | neg =>
      simp only [UnitAtom.cutoffs,List.mem_singleton] at hb
      subst b
      exact prepared_add_plain _ _ ha (prepared_const_plain 1)
    | zero => simp [UnitAtom.cutoffs] at hb
    | pos =>
      simp only [UnitAtom.cutoffs,List.mem_singleton] at hb
      subst b
      exact prepared_scale_plain _ _ ha
  | divisible m s r => simp [UnitAtom.cutoffs] at hb

theorem prepared_plain_isLinear (i : Nat) (p : Formula) (hp : PlainPreparedFormula p) :
    isLinear i p = true := by
  simp only [isLinear,rowLinear,List.all_eq_true]
  intro a ha s hs
  obtain ⟨j,hj⟩ := hp a ha s hs
  simp only [hj,summandLinear]

end LogicLineages.PermittedControl.PreparedProjection
