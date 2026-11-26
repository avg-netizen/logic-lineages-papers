module
public import LogicLineages.PermittedControl.PreparedParameterUnitProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSupportProof

@[expose] public section
namespace LogicLineages.PermittedControl.PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open NormalForm LinearRows

private theorem plain_join_formula (p q : Formula) (hp : PlainPreparedFormula p)
    (hq : PlainPreparedFormula q) : PlainPreparedFormula (.conjunction p q) := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact hp a h
  · exact hq a h

private theorem instantiate_plain (u : UnitFormula) (b : Row) (hb : PlainPreparedRow b) :
    PlainPreparedUnit u → PlainPreparedFormula (instantiate u b) := by
  induction u with
  | bot =>
    intro _ a ha
    simp [instantiate,LinearRows.atoms] at ha
  | top =>
    intro _ a ha
    simp [instantiate,LinearRows.atoms] at ha
  | atom a =>
    intro hu c hc
    simp only [instantiate,LinearRows.atoms,List.mem_singleton] at hc
    subst c
    exact prepared_instantiate_atom_plain a b (hu a (by simp [LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms])) hb
  | neg p ih => exact ih
  | conj p q ihp ihq =>
    intro h
    exact plain_join_formula _ _
      (ihp (fun a ha => h a (List.mem_append.mpr (Or.inl ha))))
      (ihq (fun a ha => h a (List.mem_append.mpr (Or.inr ha))))
  | disj p q ihp ihq =>
    intro h
    exact plain_join_formula _ _
      (ihp (fun a ha => h a (List.mem_append.mpr (Or.inl ha))))
      (ihq (fun a ha => h a (List.mem_append.mpr (Or.inr ha))))

private theorem any_plain (ps : List Formula) :
    (∀ p ∈ ps, PlainPreparedFormula p) → PlainPreparedFormula (BoundedRows.any ps) := by
  induction ps with
  | nil =>
    intro _ a ha
    simp [BoundedRows.any,LinearRows.atoms] at ha
  | cons p ps ih =>
    intro h
    have hp := h p List.mem_cons_self
    have hps := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    exact plain_join_formula p (BoundedRows.any ps) hp hps

private theorem unit_eliminate_plain (u : UnitFormula) (hu : PlainPreparedUnit u) :
    PlainPreparedFormula (unitEliminate u) := by
  unfold unitEliminate
  apply any_plain
  intro p hp
  obtain ⟨b,hb,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
  exact instantiate_plain _ _
    (prepared_add_plain _ _ (prepared_cutoffs_plain u b hu hb) (prepared_const_plain (j : Int)))
    (prepared_guarded_unit_plain u hu)

theorem preparedProjectionSyntax : PreparedProjectionSyntax := by
  intro table p hp
  have hsupport := LinearRowsSupportProof.exactOutputSupport 0 p
  exact ⟨prepared_plain_isLinear 0 p hp.1,
    unit_eliminate_plain _ (prepared_normalize_plain 0 p hp.1), hsupport,
    fun i hi => ⟨Nat.pos_of_ne_zero ((hsupport i).mp hi).1,hp.2 i ((hsupport i).mp hi).2⟩⟩

end LogicLineages.PermittedControl.PreparedProjection
