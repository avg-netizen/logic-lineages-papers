module
public import LogicLineages.PermittedControl.PreparedParameterRowsProof

@[expose] public section
namespace LogicLineages.PermittedControl.PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open NormalForm LinearRows

def PlainPreparedUnit (u : UnitFormula) : Prop :=
  ∀ a ∈ u.atoms, PlainPreparedRow a.row

private theorem formula_left {p q : Formula} (h : PlainPreparedFormula (.conjunction p q)) :
    PlainPreparedFormula p :=
  fun a ha => h a (List.mem_append.mpr (Or.inl ha))

private theorem formula_right {p q : Formula} (h : PlainPreparedFormula (.conjunction p q)) :
    PlainPreparedFormula q :=
  fun a ha => h a (List.mem_append.mpr (Or.inr ha))

private theorem unit_join (p q : UnitFormula) (hp : PlainPreparedUnit p) (hq : PlainPreparedUnit q) :
    PlainPreparedUnit (.conj p q) := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact hp a h
  · exact hq a h

private theorem unit_disjoin (p q : UnitFormula) (hp : PlainPreparedUnit p) (hq : PlainPreparedUnit q) :
    PlainPreparedUnit (.disj p q) := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact hp a h
  · exact hq a h

private theorem adjust_plain (i M : Nat) (p : Formula) :
    PlainPreparedFormula p → PlainPreparedUnit (adjust i M p) := by
  induction p with
  | truth =>
    intro _ a ha
    simp [adjust,LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms] at ha
  | falsity =>
    intro _ a ha
    simp [adjust,LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms] at ha
  | atom a =>
    intro h b hb
    simp only [adjust,LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,List.mem_singleton] at hb
    subst b
    exact prepared_adjust_atom_plain i M a (h a (by simp [LinearRows.atoms]))
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
    intro h
    exact unit_join _ _ (ihp (formula_left h)) (ihq (formula_right h))
  | disjunction p q ihp ihq =>
    intro h
    have hh : PlainPreparedFormula (.conjunction p q) := h
    exact unit_disjoin _ _ (ihp (formula_left hh)) (ihq (formula_right hh))

theorem prepared_normalize_plain (i : Nat) (p : Formula) (hp : PlainPreparedFormula p) :
    PlainPreparedUnit (normalize i p) := by
  unfold normalize
  apply unit_join
  · intro a ha
    simp only [LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,List.mem_singleton] at ha
    subst a
    exact prepared_const_plain 0
  · exact adjust_plain _ _ p hp

theorem prepared_guarded_unit_plain (u : UnitFormula) (hu : PlainPreparedUnit u) :
    PlainPreparedUnit (guarded u) := by
  unfold guarded
  apply unit_join
  · intro a ha
    simp only [LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,List.mem_singleton] at ha
    subst a
    exact prepared_const_plain 0
  · exact hu

theorem prepared_cutoffs_plain (u : UnitFormula) (b : Row)
    (hu : PlainPreparedUnit u) (hb : b ∈ cutoffs u) : PlainPreparedRow b := by
  rcases List.mem_cons.mp hb with he | h
  · subst b
    exact prepared_const_plain 0
  · obtain ⟨a,ha,hab⟩ := List.mem_flatMap.mp h
    exact prepared_cutoff_atom_plain a b (hu a ha) hab

end LogicLineages.PermittedControl.PreparedProjection
