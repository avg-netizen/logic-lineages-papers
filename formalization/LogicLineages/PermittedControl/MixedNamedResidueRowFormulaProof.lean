module
public import LogicLineages.PermittedControl.MixedNamedResidueRowTargets
import Mathlib.Data.Int.ModEq

@[expose] public section
namespace LogicLineages.PermittedControl.MixedNamedResidueRow
open PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open CountCongruenceNamedRow (requests residueAtom)
open MixedSameRankResidue (WeightedOperand weightedResidue)

private theorem rowFromPlain (m : Nat) (retain : Nat → Bool) (indices : List Nat) :
    PlainPreparedFormula (rowFrom m retain indices) := by
  induction indices with
  | nil => simp [PlainPreparedFormula,rowFrom,LinearRows.atoms]
  | cons j js ih =>
    by_cases h : retain j = true
    · intro a ha s hs
      have inRow : a = .divisible (2*m-1) (-(j : Int),[(1,.variable 1)]) ∨
          a ∈ LinearRows.atoms (rowFrom m retain js) := by
        simpa only [rowFrom,List.foldr_cons,if_pos h,residueAtom,LinearRows.atoms,
          List.singleton_append,List.mem_cons] using ha
      rcases inRow with head | tail
      · subst a
        have equal : s = (1,.variable 1) := List.mem_singleton.mp hs
        subst s
        exact ⟨1,rfl⟩
      · exact ih a tail s hs
    · simpa only [rowFrom,List.foldr_cons,if_neg h] using ih

private theorem rowFromSupport (m : Nat) (retain : Nat → Bool) (indices : List Nat) :
    ∀ i ∈ (rowFrom m retain indices).variables, i = 1 := by
  induction indices with
  | nil => simp [rowFrom,NormalForm.Formula.variables]
  | cons j js ih =>
    intro i hi
    by_cases h : retain j = true
    · have member : i = 1 ∨ i ∈ (rowFrom m retain js).variables := by
        simpa only [rowFrom,List.foldr_cons,if_pos h,residueAtom,NormalForm.Formula.variables,
          NormalForm.Atom.row,NormalForm.rowVariables,List.map_cons,List.map_nil,
          NormalForm.Summand.name,List.singleton_append,List.mem_cons] using hi
      exact member.elim id (ih i)
    · apply ih i
      simpa only [rowFrom,List.foldr_cons,if_neg h] using hi

theorem shapeAndSupport : ShapeAndSupport := by
  intro m rank c terms
  refine ⟨rowFromPlain m _ (List.range (2*m)),?_,?_,?_⟩
  · simp [requests]
  · simp [requests]
  · intro i hi
    have same := rowFromSupport m (fun j => keep m (c + weightedResidue terms j))
      (List.range (2*m)) i hi
    simp [requests,same]

private theorem residueAtomEval (m j : Nat) (hm : 0 < m) (ν : Nat → Nat) :
    (residueAtom m j).eval ν ↔ Nat.ModEq (2*m) j (ν 1) := by
  have modulus : 2*m-1+1 = 2*m := by omega
  have shift : -(j : Int) + (ν 1 : Int) = (ν 1 : Int) - j := by omega
  simp only [residueAtom,NormalForm.Formula.eval,NormalForm.Atom.eval,NormalForm.rowValue,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,NormalForm.Summand.term,
    OrdinalComparison.LayeredComparison.SnyatkovCompletion.Term.value,one_mul,add_zero,modulus]
  rw [shift]
  exact Int.modEq_iff_dvd.symm.trans Int.natCast_modEq_iff

private theorem rowFromEval (m : Nat) (retain : Nat → Bool) (ν : Nat → Nat)
    (indices : List Nat) :
    (rowFrom m retain indices).eval ν ↔
      ∃ j ∈ indices, retain j = true ∧ (residueAtom m j).eval ν := by
  induction indices with
  | nil => simp [rowFrom,NormalForm.Formula.eval]
  | cons j js ih =>
    change ((if retain j then .disjunction (residueAtom m j) (rowFrom m retain js)
      else rowFrom m retain js) : NormalForm.Formula).eval ν ↔ _
    by_cases h : retain j = true
    · rw [if_pos h]
      change ((residueAtom m j).eval ν ∨ (rowFrom m retain js).eval ν) ↔ _
      rw [ih]
      constructor
      · rintro (ha | ⟨k,hk,hkeep,ha⟩)
        · exact ⟨j,List.mem_cons_self,h,ha⟩
        · exact ⟨k,List.mem_cons_of_mem _ hk,hkeep,ha⟩
      · rintro ⟨k,hk,hkeep,ha⟩
        rcases List.mem_cons.mp hk with same | later
        · subst k
          exact Or.inl ha
        · exact Or.inr ⟨k,later,hkeep,ha⟩
    · rw [if_neg h,ih]
      constructor
      · rintro ⟨k,hk,hkeep,ha⟩
        exact ⟨k,List.mem_cons_of_mem _ hk,hkeep,ha⟩
      · rintro ⟨k,hk,hkeep,ha⟩
        rcases List.mem_cons.mp hk with same | later
        · subst k
          exact (h hkeep).elim
        · exact ⟨k,later,hkeep,ha⟩

private theorem keepExact (m : Nat) (value : Int) :
    keep m value = true ↔ (m : Int) ∣ value := by
  simp only [keep,decide_eq_true_eq]
  rw [← Nat.dvd_iff_mod_eq_zero,← Int.natAbs_dvd_natAbs,Int.natAbs_natCast]

theorem rowAt (m x : Nat) (hm : 0 < m) (c : Int) (terms : List WeightedOperand)
    (ν : Nat → Nat) (hν : ν 1 = x) :
    (row m c terms).eval ν ↔ (m : Int) ∣ c + weightedResidue terms (x%(2*m)) := by
  unfold row
  rw [rowFromEval]
  constructor
  · rintro ⟨j, hj, hkeep, ha⟩
    have smaller := List.mem_range.mp hj
    have residue := (residueAtomEval m j hm ν).mp ha
    rw [hν] at residue
    have actual : j = x%(2*m) := (Nat.mod_eq_of_lt smaller).symm.trans residue
    subst j
    exact (keepExact _ _).mp hkeep
  · intro h
    have positive : 0 < 2*m := by omega
    refine ⟨x%(2*m),List.mem_range.mpr (Nat.mod_lt _ positive),(keepExact _ _).mpr h,?_⟩
    apply (residueAtomEval m _ hm ν).mpr
    rw [hν]
    exact Nat.mod_mod _ _

end LogicLineages.PermittedControl.MixedNamedResidueRow
