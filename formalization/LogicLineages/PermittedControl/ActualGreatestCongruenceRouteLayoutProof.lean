module
public import LogicLineages.PermittedControl.ActualGreatestCongruenceRouteTargets
import LogicLineages.PermittedControl.RankResidueChoicesLayoutProof
import LogicLineages.PermittedControl.MixedRankResidueSupportProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualGreatestCongruenceRoute
open PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open MixedRankResidue (rankSupport rankSupportExact)
open RankResidueChoices (Slot namedSlots namedSlotsExact)

private theorem belowRank (top : Nat) (terms : List WeightedOperand) (j : Nat)
    (hj : j < (lowerRanks top terms).length) : (lowerRanks top terms)[j] < top :=
  decide_eq_true_eq.mp (List.mem_filter.mp (List.getElem_mem hj)).2

private theorem memberSlot (top : Nat) (terms : List WeightedOperand) (slot : Slot)
    (used : slot ∈ namedSlots (lowerRanks top terms)) :
      ∃ j : Nat, ∃ hj : j < (lowerRanks top terms).length,
        slot = (j+1,(lowerRanks top terms)[j]) := by
  obtain ⟨j,hr,frame⟩ := List.mem_map.mp used
  have hi : j < (lowerRanks top terms).length := List.mem_range.mp hr
  exact ⟨j,hi,by simpa only [List.getElem?_eq_getElem hi,Option.getD_some] using frame.symm⟩

theorem exactGreatestResidueLayout : ExactGreatestResidueLayout := by
  intro top terms
  let low := lowerRanks top terms
  refine ⟨?_,?_,?_⟩
  · intro scope t used
    rcases lt_or_eq_of_le (scope t used) with below | here
    · have rankUsed : t.2.rank ∈ rankSupport terms :=
        ((rankSupportExact.1 terms).2 t.2.rank).mpr ⟨t,used,rfl⟩
      have h : t.2.rank ∈ low := List.mem_filter.mpr ⟨rankUsed,decide_eq_true_eq.mpr below⟩
      have slot : t.2.rank ∈ (namedSlots low).map Prod.snd := (namedSlotsExact low).1 ▸ h
      exact List.mem_cons_of_mem _ slot
    · rw [here]
      exact List.mem_cons_self
  · intro slot used
    rcases List.mem_cons.mp used with same | lower
    · subst slot
      exact ⟨fun _ => rfl,fun _ => rfl⟩
    · obtain ⟨j,hj,rfl⟩ := memberSlot top terms slot lower
      exact ⟨fun h => False.elim (Nat.succ_ne_zero j h),
        fun h => False.elim ((ne_of_lt (belowRank top terms j hj)) h)⟩
  · intro slot used
    rcases List.mem_cons.mp used with same | lower
    · subst slot; exact Nat.zero_le _
    · obtain ⟨j,hj,rfl⟩ := memberSlot top terms slot lower
      simpa only [table,List.length_map] using Nat.succ_le_of_lt hj

theorem exactGreatestResidueTies : ExactGreatestResidueTies := by
  intro f baseline top terms
  let low := lowerRanks top terms
  have atSlot (j : Nat) (hj : j < (table top terms).length) :
      ∃ hi : j < low.length, (table top terms)[j] = .coordinate low[j] := by
    have hi : j < low.length := by simpa only [table,List.length_map] using hj
    exact ⟨hi,List.getElem_map ..⟩
  refine ⟨?_,?_⟩
  · let assignment : Nat → Nat := fun
      | 0 => 0
      | j+1 => baseline (low[j]?.getD 0)
    refine ⟨assignment,?_⟩
    intro j hj
    obtain ⟨hi,eq⟩ := atSlot j hj
    change (table top terms)[j].rank < top ∧
      LowerOperandActual f baseline ((table top terms)[j]) (assignment (j+1))
    rw [eq]
    refine ⟨belowRank top terms j hi,?_⟩
    change baseline (low[j]?.getD 0) = baseline low[j]
    rw [List.getElem?_eq_getElem hi,Option.getD_some]
  · intro ν tied z slot used
    rcases List.mem_cons.mp used with same | lower
    · subst slot; simp
    · obtain ⟨j,hj,rfl⟩ := memberSlot top terms slot lower
      have jTable : j < (table top terms).length := by simpa only [table,List.length_map] using hj
      obtain ⟨hi,eq⟩ := atSlot j jTable
      have hr : low[j] < top := belowRank top terms j hj
      have read := tied j jTable
      change (table top terms)[j].rank < top ∧
        LowerOperandActual f baseline ((table top terms)[j]) (ν (j+1)) at read
      rw [eq] at read
      simp only [Function.update_of_ne (Nat.succ_ne_zero j),Function.update_of_ne (ne_of_lt hr)]
      exact read.2

end LogicLineages.PermittedControl.ActualGreatestCongruenceRoute
