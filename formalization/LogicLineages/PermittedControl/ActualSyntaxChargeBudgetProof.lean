module
public import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetTargets
import LogicLineages.PermittedControl.ActualRankedRowColumnsWeightsProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationWeightsProof
import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSyntaxChargeBudget
open PreparedProjection ActualZeroClassReplacement ActualWeightedReadNormalization
open ActualRankedRowColumns InnerTerminationTargets ActualReadChargeIteration ActualFiniteGlobalTail

private theorem originalKeyBudget (raw : List Read) : (groupedWeights raw).support.card ≤ raw.length := by
  classical
  let keys := raw.map (fun rd => rd.1.2)
  have subset : (groupedWeights raw).support ⊆ keys.toFinset := by
    intro op active
    obtain ⟨rd,original,key⟩ := (exactGroupedWeights raw op).2.2 active
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨rd,original,key⟩)
  calc
    (groupedWeights raw).support.card ≤ keys.toFinset.card := Finset.card_le_card subset
    _ ≤ keys.length := List.toFinset_card_le keys
    _ = raw.length := List.length_map _

theorem exactDistinctSupportBudget : ExactDistinctSupportBudget := by
  classical
  intro r c raw
  dsimp only
  let row := rankedRow r c raw
  let counts := row.count.support.map (countOperand r)
  let values := row.value.support.map (valueOperand r)
  have coeff := exactRankedCoefficients r c raw
  have disjoint : Disjoint counts values := by
    apply Finset.disjoint_left.mpr
    intro op fromCount fromValue
    obtain ⟨k,_,asCount⟩ := Finset.mem_map.mp fromCount
    obtain ⟨v,_,asValue⟩ := Finset.mem_map.mp fromValue
    have impossible : LowerOperand.count k.2 k.1.1 k.1.2 =
        LowerOperand.ordinary v.1 v.2 := asCount.trans asValue.symm
    cases impossible
  have cntSubset : counts ⊆ (groupedWeights raw).support := by
    intro op among
    obtain ⟨k,key,present⟩ := Finset.mem_map.mp among
    subst op
    exact (coeff.2.2.2.2.1 k).mp key
  have valSubset : values ⊆ (groupedWeights raw).support := by
    intro op among
    obtain ⟨k,key,present⟩ := Finset.mem_map.mp among
    subst op
    exact ((coeff.2.2.2.2.2 k).mp key).2
  change row.count.support.card + row.value.support.card ≤ raw.length
  calc
    row.count.support.card + row.value.support.card = (counts ∪ values).card := by
      rw [Finset.card_union_of_disjoint disjoint]
      simp only [counts,values,Finset.card_map]
    _ ≤ (groupedWeights raw).support.card :=
      Finset.card_le_card (Finset.union_subset cntSubset valSubset)
    _ ≤ raw.length := originalKeyBudget raw

private theorem stateBound (r : Nat) (s : ReadState) :
    stateCharge r s ≤ syntaxBudget r (syntaxOf s) := by
  let row := rankedRow r s.constant s.reads
  have countBound : countCharge row ≤ row.count.support.card * 3 ^ r := by
    change (∑ k ∈ row.count.support, 3 ^ (k.2 : Nat)) ≤ row.count.support.card * 3 ^ r
    calc
      _ ≤ row.count.support.card • 3 ^ r :=
        Finset.sum_le_card_nsmul _ _ _ (fun k _ => Nat.pow_le_pow_right (by decide) k.2.isLt.le)
      _ = _ := by rw [smul_eq_mul]
  have valueBound : valueCount row ≤ row.value.support.card * 3 ^ r := by
    have h : 1 ≤ 3 ^ r := Nat.one_le_pow r 3 (by decide)
    change row.value.support.card ≤ row.value.support.card * 3 ^ r
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left row.value.support.card h
  have supportBound : row.count.support.card + row.value.support.card ≤ s.reads.length :=
    exactDistinctSupportBudget r s.constant s.reads
  calc
    stateCharge r s = countCharge row + valueCount row := rfl
    _ ≤ row.count.support.card * 3 ^ r + row.value.support.card * 3 ^ r :=
      Nat.add_le_add countBound valueBound
    _ = (row.count.support.card + row.value.support.card) * 3 ^ r := (Nat.add_mul _ _ _).symm
    _ ≤ s.reads.length * 3 ^ r := Nat.mul_le_mul_right _ supportBound
    _ = syntaxBudget r (syntaxOf s) := by simp only [syntaxBudget,syntaxOf,List.length_map]

private theorem zeroRank (s : ReadState) : stateCharge 0 s = 0 := by
  let row := rankedRow 0 s.constant s.reads
  have noCount : row.count.support = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k _
    exact Fin.elim0 k.2
  have noValue : row.value.support = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k _
    exact Fin.elim0 k.1
  change countCharge row + valueCount row = 0
  simp only [countCharge,valueCount,noCount,noValue,Finset.sum_empty,Finset.card_empty,zero_add]

theorem exactChargeBudget : ExactChargeBudget := by
  refine ⟨stateBound,?_,zeroRank⟩
  intro r terms
  let s : ReadState := ⟨0,terms.map (fun t => (t,0))⟩
  have bound := stateBound r s
  change syntaxCharge r terms ≤ syntaxBudget r (syntaxOf s) at bound
  simpa only [syntaxBudget,syntaxOf,s,List.length_map] using bound

end LogicLineages.PermittedControl.ActualSyntaxChargeBudget
