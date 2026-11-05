module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsSemanticProof
public import Mathlib.Tactic.Ring

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSemanticProof
open NormalForm LinearRows

theorem rowConst_value (z : Int) (ν : Nat → Nat) : rowValue (rowConst z) ν = z := by
  simp [rowConst, rowValue]

theorem rowAdd_value (r s : Row) (ν : Nat → Nat) :
    rowValue (rowAdd r s) ν = rowValue r ν + rowValue s ν := by
  simp only [rowAdd, rowValue, List.map_append, List.sum_append]
  omega

theorem rowScale_value (z : Int) (r : Row) (ν : Nat → Nat) :
    rowValue (rowScale z r) ν = z * rowValue r ν := by
  have h : (r.2.map (fun a => (z * a.1) * (a.2.term.value ν : Int))).sum =
      z * (r.2.map (fun a => a.1 * (a.2.term.value ν : Int))).sum := by
    induction r.2 with
    | nil => simp
    | cons a xs ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        ring
  simp only [rowScale, rowValue, List.map_map, Function.comp_def]
  rw [h]
  ring

theorem actualRowArithmetic : LinearRowsTargets.ActualRowArithmetic :=
  ⟨rowConst_value, rowAdd_value, rowScale_value⟩

theorem summandLinear_iff (i : Nat) (s : Summand) :
    summandLinear i s = true ↔ (s.name = i → s = Summand.variable i) := by
  cases s <;> simp [summandLinear, Summand.name]

theorem rowLinear_iff (i : Nat) (r : Row) :
    rowLinear i r = true ↔
      ∀ a ∈ r.2, a.2.name = i → a.2 = Summand.variable i := by
  simp only [rowLinear, List.all_eq_true, summandLinear_iff]

theorem exactLinearityTest : LinearRowsTargets.ExactLinearityTest := by
  intro i p
  simp only [isLinear, List.all_eq_true, rowLinear_iff]

theorem items_split (i : Nat) (xs : List (Int × Summand)) (ν : Nat → Nat) (n : Nat) :
    (∀ a ∈ xs, a.2.name = i → a.2 = Summand.variable i) →
    (xs.map (fun a => a.1 * (a.2.term.value (Function.update ν i n) : Int))).sum =
      ((xs.filter (fun a => a.2.name != i)).map
        (fun a => a.1 * (a.2.term.value ν : Int))).sum +
      (xs.map (fun a => if a.2.name = i then a.1 else 0)).sum * (n : Int) := by
  induction xs with
  | nil => intro _; simp
  | cons a xs ih =>
      intro h
      have ht : ∀ b ∈ xs, b.2.name = i → b.2 = Summand.variable i :=
        fun b hb => h b (List.mem_cons_of_mem a hb)
      rcases a with ⟨w, s⟩
      by_cases hi : s.name = i
      · have hs := h (w, s) List.mem_cons_self hi
        change s = Summand.variable i at hs
        subst s
        simpa [Summand.name, Summand.term, Term.value, Function.update_self,
          add_mul, add_assoc, add_left_comm, add_comm] using
          congrArg (fun z : Int => w * (n : Int) + z) (ih ht)
      · have hv := BoundedRowsSemanticProof.value_update_other s i n ν hi
        simp [hi, hv, ih ht, add_assoc, add_left_comm, add_comm]

theorem actualLinearRowSplit : LinearRowsTargets.ActualLinearRowSplit := by
  intro i r hr ν n
  have h := items_split i r.2 ν n ((rowLinear_iff i r).mp hr)
  simp only [rowValue, remainder, leading]
  rw [h]
  omega

theorem weight_positive (i : Nat) (a : Atom) : 0 < weight i a := by
  unfold weight
  split_ifs with h
  · exact Nat.zero_lt_one
  · exact Int.natAbs_pos.mpr h

theorem positiveCoefficientModulus : LinearRowsTargets.PositiveCoefficientModulus := by
  intro i p
  unfold coefficientModulus
  apply LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Proof.list_prod_positive
  intro n hn
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hn
  exact weight_positive i a

theorem positiveUnitPeriod : LinearRowsTargets.PositiveUnitPeriod := by
  intro u
  unfold period
  apply LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Proof.list_prod_positive
  intro n hn
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hn
  cases a <;> simp [UnitAtom.period]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSemanticProof
