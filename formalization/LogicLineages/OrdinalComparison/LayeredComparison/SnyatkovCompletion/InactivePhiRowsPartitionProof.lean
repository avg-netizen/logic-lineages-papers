module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuardsInputProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceAlgebraProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiRowsProof
open NormalForm InactivePhiRows

private theorem partition_sum (xs : List (Int × Summand)) (mask : List Bool)
    (hlen : mask.length = xs.length) (f : Int × Summand → Int) :
    (xs.map f).sum = ((keptItems mask xs).map f).sum + ((droppedItems mask xs).map f).sum := by
  induction xs generalizing mask with
  | nil => cases mask <;> simp_all [keptItems, droppedItems]
  | cons a xs ih =>
      cases mask with
      | nil => simp at hlen
      | cons b bs =>
          have hh := ih bs (by simpa using hlen)
          cases b <;> simp [keptItems, droppedItems] at hh ⊢ <;> omega

theorem exactOccurrencePartition : InactivePhiRowsTargets.ExactOccurrencePartition := by
  intro r mask hlen ν
  have hh := partition_sum r.2 mask hlen (fun a => a.1 * (a.2.term.value ν : Int))
  simp only [remaining, dropped, rowValue, zero_add]
  omega

theorem literalRetainedOccurrences : InactivePhiRowsTargets.LiteralRetainedOccurrences := by
  intro r mask
  constructor
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact (List.of_mem_zip (List.mem_filter.mp hb).1).1
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact (List.of_mem_zip (List.mem_filter.mp hb).1).1

theorem mask_spec (r : Row) (i : Nat) (mask : List Bool) (hm : mask ∈ masks i r) :
    mask.length = r.2.length ∧ onlyPhi (dropped r mask) = true ∧
      LinearRows.rowLinear i (remaining r mask) = true := by
  have h := (List.mem_filter.mp hm).2
  simpa only [admissible, Bool.and_eq_true, beq_iff_eq, and_assoc] using h

private theorem onlyPhi_plain (xs : List (Int × Summand)) (h : onlyPhi (0, xs) = true) :
    PlainPhiDominance.isPlain (0, xs) = true := by
  apply List.all_eq_true.mpr
  intro a ha
  have hh := List.all_eq_true.mp h a ha
  rcases a with ⟨w, s⟩
  cases s <;> simp_all [onlyPhi, PlainPhiDominance.isPlain]

private theorem onlyPhi_linearPart (xs : List (Int × Summand))
    (h : onlyPhi (0, xs) = true) (ν : Nat → Nat) :
    PlainPhiDominance.linearPart (0, xs) ν = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      have hh := Bool.and_eq_true_iff.mp h
      have hi := ih hh.2
      rcases a with ⟨w, s⟩
      cases s <;> simp_all [onlyPhi, PlainPhiDominance.linearPart]

theorem guardedValuePreservation : InactivePhiRowsTargets.GuardedValuePreservation := by
  intro r i mask hm ν hg
  have hs := mask_spec r i mask hm
  have hc := (ShiftedInputGuardsProof.actualCancellationGuard (dropped r mask) ν).mp hg
  have hd := PlainPhiDominanceProof.actualCancelledRow (dropped r mask)
    (onlyPhi_plain _ hs.2.1) ν hc
  have hz : rowValue (dropped r mask) ν = 0 :=
    hd.trans (onlyPhi_linearPart _ hs.2.1 ν)
  have hp := exactOccurrencePartition r mask hs.1 ν
  omega

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiRowsProof
