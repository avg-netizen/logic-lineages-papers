module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitGadgetRowsProof
public import Mathlib.Algebra.BigOperators.Fin
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitLinear.Proof
open Polynomial Narendran

private theorem row_append (p : Nat → NPolynomial) (a b : Row) :
    rowPolynomial p (a++b) = rowPolynomial p a+rowPolynomial p b := by
  simp [rowPolynomial]

private theorem scalar_sum (p : Nat → NPolynomial) (n : Nat) :
    rowPolynomial p ((List.range n).map (wireMonomial 1 0)) =
      signed (∑ i : Fin n, p i.val) := by
  induction n with
  | zero => simp [rowPolynomial,signed]
  | succ n ih =>
      rw [List.range_succ,List.map_append,row_append,ih,Fin.sum_univ_castSucc]
      simp [rowPolynomial,monomialPolynomial,wireMonomial,Narendran.Proof.signed_add]

private theorem signed_injective : Function.Injective signed := by
  exact Polynomial.map_injective (Nat.castRingHom Int) Nat.cast_injective

/-- The literal rows retain the same scalar family and seven geometric witnesses. -/
theorem constant_rows_equations (p : Nat → NPolynomial) (n aux : Nat) :
    RowsSolve p (constantRows n aux) ↔
      ConstantGadget (p aux) (fun i : Fin 7 => p (aux+2+i.val)) ∧
        (∑ i : Fin n, p i.val) + p (aux+1) = p aux := by
  constructor
  · intro h
    simp only [RowsSolve,constantRows,List.forall_mem_cons,List.forall_mem_nil,and_true] at h
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := h
    rw [row_append,scalar_sum] at h6
    norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant] at h1 h2 h3 h4 h5 h6
    refine ⟨?_,?_⟩
    · norm_num [ConstantGadget,Nat.add_assoc]
      refine ⟨?_,?_,?_,?_,?_⟩
      · linear_combination h1
      · linear_combination h2
      · linear_combination h3
      · linear_combination h4
      · linear_combination h5
    · apply signed_injective
      rw [Narendran.Proof.signed_add]
      linear_combination h6
  · rintro ⟨hg,hs⟩
    norm_num [ConstantGadget,Nat.add_assoc] at hg
    obtain ⟨h1,h2,h3,h4,h5⟩ := hg
    have h6 := congrArg signed hs
    rw [Narendran.Proof.signed_add] at h6
    simp only [RowsSolve,constantRows,List.forall_mem_cons,List.forall_mem_nil,and_true]
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant]
      linear_combination h1
    · norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant]
      linear_combination h2
    · norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant]
      linear_combination h3
    · norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant]
      linear_combination h4
    · norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant]
      linear_combination h5
    · rw [row_append,scalar_sum]
      norm_num [rowPolynomial,monomialPolynomial,wireMonomial,constant]
      linear_combination h6

/-- No condition is imposed on polynomial witness slots outside the scalar block. -/
theorem constant_rows_force_scalars : CircuitGadgetTargets.ConstantRowsForceScalars := by
  intro p n aux h i hi
  have ⟨hg,hs⟩ := (constant_rows_equations p n aux).mp h
  have hsimp : SimultaneousConstantGadget (fun i : Fin n => p i.val) :=
    ⟨p aux,p (aux+1),(fun i : Fin 7 => p (aux+2+i.val)),hg,hs⟩
  exact (Narendran.Proof.exactSimultaneousConstants n (fun i : Fin n => p i.val)).mp hsimp ⟨i,hi⟩

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitLinear.Proof
