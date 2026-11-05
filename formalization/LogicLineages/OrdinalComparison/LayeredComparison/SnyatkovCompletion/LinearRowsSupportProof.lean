module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSupportProof
open NormalForm LinearRows

def unitVariables : UnitFormula → List Nat
  | .bot | .top => []
  | .atom a => rowVariables a.row
  | .neg p => unitVariables p
  | .conj p q | .disj p q => unitVariables p ++ unitVariables q

theorem row_const_variables (z : Int) : rowVariables (rowConst z) = [] := rfl

theorem row_add_variables (r s : Row) :
    rowVariables (rowAdd r s) = rowVariables r ++ rowVariables s := by
  simp only [rowVariables, rowAdd, List.map_append]

theorem row_scale_variables (z : Int) (r : Row) :
    rowVariables (rowScale z r) = rowVariables r := by
  simp only [rowVariables, rowScale, List.map_map, Function.comp_def]

theorem row_remainder_variables (i : Nat) (r : Row) (v : Nat) :
    v ∈ rowVariables (remainder i r) ↔ v ≠ i ∧ v ∈ rowVariables r := by
  constructor
  · intro hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    have h := List.mem_filter.mp ha
    exact ⟨by simpa only [bne_iff_ne] using h.2,
      List.mem_map.mpr ⟨a, h.1, rfl⟩⟩
  · rintro ⟨hname, hv⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact List.mem_map.mpr ⟨a,
      List.mem_filter.mpr ⟨ha, by simpa only [bne_iff_ne] using hname⟩, rfl⟩

theorem unit_variables_atoms (u : UnitFormula) :
    unitVariables u = u.atoms.flatMap (fun a => rowVariables a.row) := by
  induction u with
  | bot => rfl
  | top => rfl
  | atom a => simp [unitVariables,
      LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms]
  | neg p ih => exact ih
  | conj p q ihp ihq => simp [unitVariables,
      LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
      List.flatMap_append, ihp, ihq]
  | disj p q ihp ihq => simp [unitVariables,
      LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
      List.flatMap_append, ihp, ihq]

theorem adjust_atom_variables (i M : Nat) (a : Atom) (v : Nat) :
    v ∈ rowVariables (adjustAtom i M a).row ↔ v ≠ i ∧ v ∈ rowVariables a.row := by
  cases a with
  | nonnegative r =>
      simp only [adjustAtom]
      split <;> simp only [UnitAtom.row, row_scale_variables, Atom.row,
        row_remainder_variables]
  | divisible m r =>
      simp only [adjustAtom]
      split <;> simp only [UnitAtom.row, row_scale_variables, Atom.row,
        row_remainder_variables]

theorem adjust_variables (i M : Nat) (p : Formula) (v : Nat) :
    v ∈ unitVariables (adjust i M p) ↔ v ≠ i ∧ v ∈ p.variables := by
  induction p with
  | truth => simp [adjust, unitVariables, Formula.variables]
  | falsity => simp [adjust, unitVariables, Formula.variables]
  | atom a => exact adjust_atom_variables i M a v
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
      simp only [adjust, unitVariables, Formula.variables, List.mem_append, ihp, ihq]
      tauto
  | disjunction p q ihp ihq =>
      simp only [adjust, unitVariables, Formula.variables, List.mem_append, ihp, ihq]
      tauto

theorem normalize_variables (i : Nat) (p : Formula) (v : Nat) :
    v ∈ unitVariables (normalize i p) ↔ v ≠ i ∧ v ∈ p.variables := by
  simpa only [normalize, unitVariables, UnitAtom.row, row_const_variables,
    List.nil_append] using adjust_variables i (coefficientModulus i p) p v

theorem instantiate_atom_variables (a : UnitAtom) (b : Row) (v : Nat) :
    v ∈ rowVariables (a.instantiate b).row ↔
      v ∈ rowVariables b ∨ v ∈ rowVariables a.row := by
  cases a <;> simp only [UnitAtom.instantiate, Atom.row, UnitAtom.row,
    row_add_variables, row_scale_variables, List.mem_append]

theorem instantiate_contains (u : UnitFormula) (b : Row) (v : Nat) :
    v ∈ unitVariables u → v ∈ (instantiate u b).variables := by
  induction u with
  | bot => simp [unitVariables]
  | top => simp [unitVariables]
  | atom a =>
      intro hv
      exact (instantiate_atom_variables a b v).mpr (Or.inr hv)
  | neg p ih => exact ih
  | conj p q ihp ihq =>
      simpa only [unitVariables, instantiate, Formula.variables, List.mem_append]
        using Or.imp ihp ihq
  | disj p q ihp ihq =>
      simpa only [unitVariables, instantiate, Formula.variables, List.mem_append]
        using Or.imp ihp ihq

theorem instantiate_subset (u : UnitFormula) (b : Row) (v : Nat) :
    v ∈ (instantiate u b).variables →
      v ∈ rowVariables b ∨ v ∈ unitVariables u := by
  induction u with
  | bot => simp [instantiate, Formula.variables]
  | top => simp [instantiate, Formula.variables]
  | atom a => exact (instantiate_atom_variables a b v).mp
  | neg p ih => exact ih
  | conj p q ihp ihq =>
      simp only [instantiate, Formula.variables, unitVariables, List.mem_append] at *
      tauto
  | disj p q ihp ihq =>
      simp only [instantiate, Formula.variables, unitVariables, List.mem_append] at *
      tauto

theorem guarded_variables (u : UnitFormula) : unitVariables (guarded u) = unitVariables u := by
  simp only [guarded, unitVariables, UnitAtom.row, row_const_variables, List.nil_append]

theorem cutoff_atom_subset (a : UnitAtom) (b : Row) (v : Nat)
    (hb : b ∈ a.cutoffs) : v ∈ rowVariables b → v ∈ rowVariables a.row := by
  cases a with
  | nonnegative s r =>
      cases s with
      | neg =>
        simp only [UnitAtom.cutoffs, List.mem_singleton] at hb
        subst b
        simp only [row_add_variables, row_const_variables, List.append_nil, UnitAtom.row]
        exact id
      | zero => simp only [UnitAtom.cutoffs, List.not_mem_nil] at hb
      | pos =>
        simp only [UnitAtom.cutoffs, List.mem_singleton] at hb
        subst b
        simpa only [row_scale_variables, UnitAtom.row] using (id :
          v ∈ rowVariables r → v ∈ rowVariables r)
  | divisible m s r => simp only [UnitAtom.cutoffs, List.not_mem_nil] at hb

theorem cutoff_subset (u : UnitFormula) (b : Row) (v : Nat)
    (hb : b ∈ cutoffs u) : v ∈ rowVariables b → v ∈ unitVariables u := by
  rcases List.mem_cons.mp hb with hb | hb
  · subst b
    simp only [row_const_variables, List.not_mem_nil, false_implies]
  · obtain ⟨a, ha, hab⟩ := List.mem_flatMap.mp hb
    intro hv
    rw [unit_variables_atoms]
    exact List.mem_flatMap.mpr ⟨a, ha, cutoff_atom_subset a b v hab hv⟩

private theorem unit_period_positive (u : UnitFormula) : 0 < period u := by
  unfold period
  induction u.atoms with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.prod_cons]
      exact Nat.mul_pos (by cases a <;> simp [UnitAtom.period]) ih

theorem unit_eliminate_variables (u : UnitFormula) (v : Nat) :
    v ∈ (unitEliminate u).variables ↔ v ∈ unitVariables u := by
  rw [unitEliminate, BoundedRowsSemanticProof.any_variables]
  constructor
  · rintro ⟨p, hp, hv⟩
    obtain ⟨b, hb, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
    rcases instantiate_subset (guarded u) (rowAdd b (rowConst (j : Int))) v hv with hv | hv
    · have hvb : v ∈ rowVariables b := by
        simpa only [row_add_variables, row_const_variables, List.append_nil] using hv
      exact cutoff_subset u b v hb hvb
    · simpa only [guarded_variables] using hv
  · intro hv
    refine ⟨instantiate (guarded u) (rowAdd (rowConst 0) (rowConst (0 : Int))), ?_, ?_⟩
    · refine List.mem_flatMap.mpr ⟨rowConst 0, List.mem_cons_self, ?_⟩
      refine List.mem_map.mpr ⟨(0 : Int), ?_, rfl⟩
      exact List.mem_flatMap.mpr ⟨(0 : Nat), List.mem_range.mpr (unit_period_positive u),
        List.mem_singleton.mpr rfl⟩
    · apply instantiate_contains
      simpa only [guarded_variables] using hv

theorem exactOutputSupport : LinearRowsTargets.ExactOutputSupport := by
  intro i p v
  exact (unit_eliminate_variables (normalize i p) v).trans (normalize_variables i p v)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSupportProof
