module
public import LogicLineages.PermittedControl.MixedSameRankResidueTargets
import LogicLineages.PermittedControl.MixedSameRankResidueCodeProof
import LogicLineages.PermittedControl.OrdinaryResidueOperandStatementChecks
import LogicLineages.PermittedControl.EntryResiduesProof
import LogicLineages.PermittedControl.ShortFieldGapProof
import LogicLineages.PermittedControl.PreparedParameterActualProof
import LogicLineages.OrdinalComparison.OrdinalRepresentationSound
import Mathlib.Data.Int.ModEq

@[expose] public section
namespace LogicLineages.PermittedControl.MixedSameRankResidue
open OrdinalComparison FieldComparison PreparedProjection
open StatementChecks (fixed_ordinaryResidueOperandActual fixed_ordinaryResidueOperandCodeExact)

private theorem countRead (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (m rank : Nat) (lam mu : NONote) (ρ : Nat → Nat) (hm : 0 < m)
    (proper : ProperField (.entry 0 lam mu))
    (tail : operandTail B m (.count rank lam mu) ≤ ρ rank) :
    ∃ v : Nat,
      LowerOperandActual f ρ (.count rank lam mu) v ∧
      lowerOperandRead f ρ (.count rank lam mu) = some (some v) ∧
      Int.ModEq (m : Int) (v : Int) (operandResidue (ρ rank % (2*m)) (.count rank lam mu)) := by
  let x := ρ rank
  let j := x % (2*m)
  let k := shortGapLength lam mu
  let norm := actualOrdinalNorm mu.1.repr
  have bound : max (actualOrdinalNorm lam.1.repr) (max (norm+3) (max m B)) ≤ x := tail
  obtain ⟨i,first,_,onShort,onLong⟩ :=
    entryResidues f B hf m lam.1.repr mu.1.repr x hm
      (rawNotation_repr_lt_epsilonZero lam.1) proper.1 proper.2.1 proper.2.2 bound
  have dom : ClosedOrdinaryValueDomain (.entry 0 lam mu) x :=
    ⟨proper,(le_max_left _ _).trans bound⟩
  have actual : LowerOperandActual f ρ (.count rank lam mu) i := ⟨dom,first⟩
  refine ⟨i,actual,(preparedTiedProjection.1 f ρ (.count rank lam mu) i).mpr actual,?_⟩
  change Int.ModEq (m : Int) (i : Int) (CountCongruenceNamedRow.residueCount k norm j)
  by_cases zero : k = 0
  · have long : ¬ ∃ l : Nat, 0 < l ∧
        lam.1.repr = mu.1.repr + Ordinal.omega0 * (l : Ordinal) := by
      rintro ⟨l,positive,gap⟩
      have same : k = l := (shortGapRecognition lam mu proper l positive).2.2.mpr gap
      exact (Nat.ne_of_gt positive) (same.symm.trans zero)
    have hfloors : Int.ModEq (m : Int) (potential x : Int) ((j/2 : Nat) : Int) := by
      apply Int.natCast_modEq_iff.mpr
      change (x/2)%m = (j/2)%m
      calc
        (x/2)%m = ((x/2)%m)%m := (Nat.mod_mod (x/2) m).symm
        _ = (j/2)%m := congrArg (fun n : Nat => n%m) (Nat.mod_mul_right_div_self x 2 m).symm
    simpa only [CountCongruenceNamedRow.residueCount,if_pos zero] using
      (onLong long).1.trans (hfloors.sub_right (((norm+1)/2 : Nat) : Int))
  · have positive : 0 < k := Nat.pos_of_ne_zero zero
    have shape := (shortGapRecognition lam mu proper k positive).2.2.mp rfl
    have exactCount := onShort k positive shape
    rw [CountCongruenceNamedRow.residueCount,if_neg zero,exactCount]

private theorem operandRead (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (m rank : Nat) (ρ : Nat → Nat) (hm : 0 < m) (op : LowerOperand)
    (hr : op.rank = rank) (proper : properOperand op) (tail : operandTail B m op ≤ ρ rank) :
    ∃ v : Nat, LowerOperandActual f ρ op v ∧ lowerOperandRead f ρ op = some (some v) ∧
      Int.ModEq (m : Int) (v : Int) (operandResidue (ρ rank % (2*m)) op) := by
  cases op with
  | coordinate r =>
    change r = rank at hr
    subst r
    refine ⟨ρ rank,rfl,rfl,?_⟩
    apply Int.natCast_modEq_iff.mpr
    exact (Nat.mod_mod_of_dvd (ρ rank) (Nat.dvd_mul_left m 2)).symm
  | ordinary r F =>
    change r = rank at hr
    subst r
    have originally : OrdinaryResidueOperand.residueTailCode B m (longFieldCode F) ≤ ρ rank := by
      rw [fixed_ordinaryResidueOperandCodeExact.2.2.2 B m F]
      exact tail
    obtain ⟨v,actual,read,residue⟩ := fixed_ordinaryResidueOperandActual
      f B hf m rank F ρ hm proper originally
    refine ⟨v,actual,read,?_⟩
    exact residue.of_dvd ⟨2,mul_comm 2 (m : Int)⟩
  | count r lam mu =>
    change r = rank at hr
    subst r
    exact countRead f B hf m rank lam mu ρ hm proper tail

private theorem readSum (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (m rank : Nat) (ρ : Nat → Nat) (hm : 0 < m) (terms : List WeightedOperand)
    (typed : ∀ t ∈ terms, t.2.rank = rank ∧ properOperand t.2)
    (tail : weightedTail B m terms ≤ ρ rank) :
    ∃ values : List Nat,
      orderedReads f ρ terms values ∧
      Int.ModEq (m : Int) (actualSum terms values) (weightedResidue terms (ρ rank % (2*m))) := by
  induction terms with
  | nil => exact ⟨[],True.intro,Int.ModEq.refl _⟩
  | cons t ts ih =>
    obtain ⟨rankOf,proper⟩ := typed t List.mem_cons_self
    change max (operandTail B m t.2) (weightedTail B m ts) ≤ ρ rank at tail
    obtain ⟨v,actual,read,cong⟩ :=
      operandRead f B hf m rank ρ hm t.2 rankOf proper ((le_max_left _ _).trans tail)
    obtain ⟨vs,reads,rest⟩ :=
      ih (fun u hu => typed u (List.mem_cons_of_mem _ hu)) ((le_max_right _ _).trans tail)
    refine ⟨v::vs,⟨actual,read,reads⟩,?_⟩
    change Int.ModEq (m : Int) (t.1 * (v : Int) + actualSum ts vs)
      (t.1 * operandResidue (ρ rank % (2*m)) t.2 + weightedResidue ts (ρ rank % (2*m)))
    exact (cong.mul_left t.1).add rest

theorem actualWeightedResidue : ActualWeightedResidue := by
  intro f B hf m rank c terms ρ hm typed bound
  rw [weightedTailLiteral B m terms] at bound
  obtain ⟨values,reads,cong⟩ := readSum f B hf m rank ρ hm terms typed bound
  exact ⟨values,reads,cong.add_left c⟩

end LogicLineages.PermittedControl.MixedSameRankResidue
