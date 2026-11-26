module
public import LogicLineages.PermittedControl.OrdinaryResidueOperandTargets
import LogicLineages.PermittedControl.OrdinaryResidueOperandCodeProof
import LogicLineages.PermittedControl.EntryTableProof
import LogicLineages.PermittedControl.ShortFieldGapProof
import LogicLineages.PermittedControl.PreparedParameterActualProof
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound
import Mathlib.Data.Int.ModEq

@[expose] public section
namespace LogicLineages.PermittedControl.OrdinaryResidueOperand
open OrdinalComparison FieldComparison PreparedProjection

private theorem moduloLiteral (m x : Nat) :
    Int.ModEq (2 * (m : Int)) (x : Int) ((x % (2*m) : Nat) : Int) := by
  have eq : Nat.ModEq (2*m) x (x % (2*m)) := (Nat.mod_mod x (2*m)).symm
  simpa only [Int.natCast_mul,Int.natCast_ofNat] using (Int.natCast_modEq_iff.mpr eq)

private theorem moduloFloor (m x a : Nat) :
    Int.ModEq (2 * (m : Int)) (2 * (potential x : Int) - 2 * (a : Int))
      (doubledFloor (x % (2*m)) a) := by
  let j := x % (2*m)
  have half : Int.ModEq (m : Int) (potential x : Int) ((j / 2 : Nat) : Int) := by
    apply Int.natCast_modEq_iff.mpr
    change (x/2)%m = (j/2)%m
    calc
      (x/2)%m = ((x/2)%m)%m := (Nat.mod_mod (x/2) m).symm
      _ = (j/2)%m := congrArg (fun n : Nat => n%m) (Nat.mod_mul_right_div_self x 2 m).symm
  exact (half.mul_left' (c := 2)).sub_right (2 * (a : Int))

private theorem valueAt (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (m x : Nat) (F : ValueField) (hm : 0 < m) (proper : ProperField F)
    (tail : residueTail B m F ≤ x) :
    ∃ v : Nat, ClosedOrdinaryValueDomain F x ∧ FieldValue f F x v ∧
      Int.ModEq (2 * (m : Int)) (v : Int) (residue F (x % (2*m))) := by
  cases F with
  | iterate a =>
    cases a with
    | zero =>
      exact ⟨x,True.intro,by simp [FieldValue],moduloLiteral m x⟩
    | succ a =>
      change max m B ≤ x at tail
      exact ⟨f^[a+1] x,True.intro,rfl,
        (bare_iterate_residue f B hf m x (a+1) hm tail (Nat.succ_pos a)).trans
          (moduloFloor m x (a+1))⟩
  | entry a lam mu =>
    have hx : max (actualOrdinalNorm lam.1.repr) (max (actualOrdinalNorm mu.1.repr+3) (max m B)) ≤ x :=
      tail
    have properZero : ProperField (.entry 0 lam mu) := proper
    have eps := rawNotation_repr_lt_epsilonZero lam.1
    obtain ⟨i,first,_,_,_⟩ :=
      entryResidues f B hf m lam.1.repr mu.1.repr x hm eps
        proper.1 proper.2.1 proper.2.2 hx
    let v := f^[a] (entryNormAt f (countInitial lam.1.repr x) i)
    refine ⟨v,⟨proper,(le_max_left _ _).trans hx⟩,⟨i,first,rfl⟩,?_⟩
    have table := derivedEntryTable f B hf m lam.1.repr mu.1.repr x i hm eps
      proper.1 proper.2.1 proper.2.2 hx first
    let k := shortGapLength lam mu
    by_cases zero : k = 0
    · have long : ¬ ∃ l : Nat, 0 < l ∧
          lam.1.repr = mu.1.repr + Ordinal.omega0 * (l : Ordinal) := by
        rintro ⟨l,positive,gap⟩
        have same : k = l := (shortGapRecognition lam mu properZero l positive).2.2.mpr gap
        exact (Nat.ne_of_gt positive) (same.symm.trans zero)
      simpa only [residue,show shortGapLength lam mu = 0 from zero,if_true,doubledCeiling] using
        (table.2 long).2.1 a
    · have positive : 0 < k := Nat.pos_of_ne_zero zero
      have gap := (shortGapRecognition lam mu properZero k positive).2.2.mp rfl
      have before := (table.1 k positive gap).2.1 a
      have after : Int.ModEq (2 * (m : Int)) (v : Int)
          (2 * (potential x : Int) - 2 * ((k+a : Nat) : Int)) := by
        simpa only [Int.natCast_add] using before
      simpa only [residue,show shortGapLength lam mu ≠ 0 from zero,if_false] using
        after.trans (moduloFloor m x (k+a))

theorem actualResidue : ActualResidue := by
  intro f B hf m rank F ρ hm proper tail
  rw [tailLiteral B m F] at tail
  obtain ⟨v,domain,value,modulo⟩ := valueAt f B hf m (ρ rank) F hm proper tail
  have actual : LowerOperandActual f ρ (.ordinary rank F) v := ⟨domain,value⟩
  exact ⟨v,actual,(preparedTiedProjection.1 f ρ (.ordinary rank F) v).mpr actual,modulo⟩

end LogicLineages.PermittedControl.OrdinaryResidueOperand
