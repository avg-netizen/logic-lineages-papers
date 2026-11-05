module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockProof
open NormalForm LinearRows

def rowOccurrences (r : Row) : List Summand := r.2.map Prod.snd

def unitOccurrences : UnitFormula → List Summand
  | .bot | .top => []
  | .atom a => rowOccurrences a.row
  | .neg p => unitOccurrences p
  | .conj p q | .disj p q => unitOccurrences p ++ unitOccurrences q

theorem row_const_occurrences (z : Int) : rowOccurrences (rowConst z) = [] := rfl

theorem row_add_occurrences (r s : Row) :
    rowOccurrences (rowAdd r s) = rowOccurrences r ++ rowOccurrences s := by
  simp only [rowOccurrences, rowAdd, List.map_append]

theorem row_scale_occurrences (z : Int) (r : Row) :
    rowOccurrences (rowScale z r) = rowOccurrences r := by
  simp only [rowOccurrences, rowScale, List.map_map, Function.comp_def]

theorem row_remainder_occurrences (i : Nat) (r : Row) (s : Summand) :
    s ∈ rowOccurrences (remainder i r) ↔ s.name ≠ i ∧ s ∈ rowOccurrences r := by
  constructor
  · intro hs
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
    have h := List.mem_filter.mp ha
    exact ⟨by simpa only [bne_iff_ne] using h.2,
      List.mem_map.mpr ⟨a, h.1, rfl⟩⟩
  · rintro ⟨hname, hs⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
    exact List.mem_map.mpr ⟨a,
      List.mem_filter.mpr ⟨ha, by simpa only [bne_iff_ne] using hname⟩, rfl⟩

theorem unit_occurrences_atoms (u : UnitFormula) :
    unitOccurrences u = u.atoms.flatMap (fun a => rowOccurrences a.row) := by
  induction u with
  | bot => rfl
  | top => rfl
  | atom a => simp [unitOccurrences,
      LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms]
  | neg p ih => exact ih
  | conj p q ihp ihq => simp [unitOccurrences,
      LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
      List.flatMap_append, ihp, ihq]
  | disj p q ihp ihq => simp [unitOccurrences,
      LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
      List.flatMap_append, ihp, ihq]

theorem adjust_atom_occurrences (i M : Nat) (a : Atom) (s : Summand) :
    s ∈ rowOccurrences (adjustAtom i M a).row ↔
      s.name ≠ i ∧ s ∈ rowOccurrences a.row := by
  cases a with
  | nonnegative r =>
      simp only [adjustAtom]
      split <;> simp only [UnitAtom.row, row_scale_occurrences, Atom.row,
        row_remainder_occurrences]
  | divisible m r =>
      simp only [adjustAtom]
      split <;> simp only [UnitAtom.row, row_scale_occurrences, Atom.row,
        row_remainder_occurrences]

theorem adjust_occurrences (i M : Nat) (p : Formula) (s : Summand) :
    s ∈ unitOccurrences (adjust i M p) ↔
      s.name ≠ i ∧ s ∈ LinearBlock.occurrences p := by
  induction p with
  | truth => simp [adjust, unitOccurrences, LinearBlock.occurrences, atoms]
  | falsity => simp [adjust, unitOccurrences, LinearBlock.occurrences, atoms]
  | atom a =>
      simpa [adjust, unitOccurrences, LinearBlock.occurrences, atoms, rowOccurrences] using adjust_atom_occurrences i M a s
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
      simp only [adjust, unitOccurrences, LinearBlock.occurrences, atoms,
        List.flatMap_append, List.mem_append] at *
      tauto
  | disjunction p q ihp ihq =>
      simp only [adjust, unitOccurrences, LinearBlock.occurrences, atoms,
        List.flatMap_append, List.mem_append] at *
      tauto

theorem normalize_occurrences (i : Nat) (p : Formula) (s : Summand) :
    s ∈ unitOccurrences (normalize i p) ↔
      s.name ≠ i ∧ s ∈ LinearBlock.occurrences p := by
  simpa only [normalize, unitOccurrences, UnitAtom.row, row_const_occurrences,
    List.nil_append] using adjust_occurrences i (coefficientModulus i p) p s

theorem instantiate_atom_occurrences (a : UnitAtom) (b : Row) (s : Summand) :
    s ∈ rowOccurrences (a.instantiate b).row ↔
      s ∈ rowOccurrences b ∨ s ∈ rowOccurrences a.row := by
  cases a <;> simp only [UnitAtom.instantiate, Atom.row, UnitAtom.row,
    row_add_occurrences, row_scale_occurrences, List.mem_append]

theorem instantiate_contains (u : UnitFormula) (b : Row) (s : Summand) :
    s ∈ unitOccurrences u → s ∈ LinearBlock.occurrences (instantiate u b) := by
  induction u with
  | bot => simp [unitOccurrences]
  | top => simp [unitOccurrences]
  | atom a =>
      intro hs
      simpa [LinearBlock.occurrences, atoms, instantiate, rowOccurrences] using
        (instantiate_atom_occurrences a b s).mpr (Or.inr hs)
  | neg p ih => exact ih
  | conj p q ihp ihq =>
      simpa only [unitOccurrences, instantiate, LinearBlock.occurrences, atoms,
        List.flatMap_append, List.mem_append] using Or.imp ihp ihq
  | disj p q ihp ihq =>
      simpa only [unitOccurrences, instantiate, LinearBlock.occurrences, atoms,
        List.flatMap_append, List.mem_append] using Or.imp ihp ihq

theorem instantiate_subset (u : UnitFormula) (b : Row) (s : Summand) :
    s ∈ LinearBlock.occurrences (instantiate u b) →
      s ∈ rowOccurrences b ∨ s ∈ unitOccurrences u := by
  induction u with
  | bot => simp [instantiate, LinearBlock.occurrences, atoms]
  | top => simp [instantiate, LinearBlock.occurrences, atoms]
  | atom a =>
      simpa [instantiate, unitOccurrences, LinearBlock.occurrences, atoms, rowOccurrences] using
        (instantiate_atom_occurrences a b s).mp
  | neg p ih => exact ih
  | conj p q ihp ihq =>
      simp only [instantiate, LinearBlock.occurrences, atoms, unitOccurrences,
        List.flatMap_append, List.mem_append] at *
      tauto
  | disj p q ihp ihq =>
      simp only [instantiate, LinearBlock.occurrences, atoms, unitOccurrences,
        List.flatMap_append, List.mem_append] at *
      tauto

theorem guarded_occurrences (u : UnitFormula) : unitOccurrences (guarded u) = unitOccurrences u := by
  simp only [guarded, unitOccurrences, UnitAtom.row, row_const_occurrences, List.nil_append]

theorem cutoff_atom_subset (a : UnitAtom) (b : Row) (s : Summand)
    (hb : b ∈ a.cutoffs) : s ∈ rowOccurrences b → s ∈ rowOccurrences a.row := by
  cases a with
  | nonnegative sign r =>
      cases sign with
      | neg =>
        simp only [UnitAtom.cutoffs, List.mem_singleton] at hb
        subst b
        simp only [row_add_occurrences, row_const_occurrences, List.append_nil, UnitAtom.row]
        exact id
      | zero => simp only [UnitAtom.cutoffs, List.not_mem_nil] at hb
      | pos =>
        simp only [UnitAtom.cutoffs, List.mem_singleton] at hb
        subst b
        simpa only [row_scale_occurrences, UnitAtom.row] using
          (id : s ∈ rowOccurrences r → s ∈ rowOccurrences r)
  | divisible m sign r => simp only [UnitAtom.cutoffs, List.not_mem_nil] at hb

theorem cutoff_subset (u : UnitFormula) (b : Row) (s : Summand)
    (hb : b ∈ cutoffs u) : s ∈ rowOccurrences b → s ∈ unitOccurrences u := by
  rcases List.mem_cons.mp hb with hb | hb
  · subst b
    simp only [row_const_occurrences, List.not_mem_nil, false_implies]
  · obtain ⟨a, ha, hab⟩ := List.mem_flatMap.mp hb
    intro hs
    rw [unit_occurrences_atoms]
    exact List.mem_flatMap.mpr ⟨a, ha, cutoff_atom_subset a b s hab hs⟩

theorem any_occurrences (ps : List Formula) (s : Summand) :
    s ∈ LinearBlock.occurrences (BoundedRows.any ps) ↔
      ∃ p ∈ ps, s ∈ LinearBlock.occurrences p := by
  induction ps with
  | nil => simp [BoundedRows.any, LinearBlock.occurrences, atoms]
  | cons p ps ih =>
      simpa only [BoundedRows.any, List.foldr_cons, LinearBlock.occurrences, atoms,
        List.flatMap_append, List.mem_append, List.mem_cons, exists_eq_or_imp] using
        or_congr Iff.rfl ih

theorem unit_eliminate_occurrences (u : UnitFormula) (s : Summand) :
    s ∈ LinearBlock.occurrences (unitEliminate u) ↔ s ∈ unitOccurrences u := by
  rw [unitEliminate, any_occurrences]
  constructor
  · rintro ⟨p, hp, hs⟩
    obtain ⟨b, hb, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hp
    rcases instantiate_subset (guarded u) (rowAdd b (rowConst (j : Int))) s hs with hs | hs
    · have hsb : s ∈ rowOccurrences b := by
        simpa only [row_add_occurrences, row_const_occurrences, List.append_nil] using hs
      exact cutoff_subset u b s hb hsb
    · simpa only [guarded_occurrences] using hs
  · intro hs
    refine ⟨instantiate (guarded u) (rowAdd (rowConst 0) (rowConst (0 : Int))), ?_, ?_⟩
    · refine List.mem_flatMap.mpr ⟨rowConst 0, List.mem_cons_self, ?_⟩
      refine List.mem_map.mpr ⟨(0 : Int), ?_, rfl⟩
      have hpos : 0 < period u := by
        unfold period
        induction u.atoms with
        | nil => simp
        | cons a as ih =>
            simp only [List.map_cons, List.prod_cons]
            exact Nat.mul_pos (by cases a <;> simp [UnitAtom.period]) ih
      exact List.mem_flatMap.mpr ⟨(0 : Nat), List.mem_range.mpr hpos,
        List.mem_singleton.mpr rfl⟩
    · apply instantiate_contains
      simpa only [guarded_occurrences] using hs

theorem exactOneNameOccurrences : LinearBlockTargets.ExactOneNameOccurrences := by
  intro i p s
  exact (unit_eliminate_occurrences (normalize i p) s).trans (normalize_occurrences i p s)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlockProof
