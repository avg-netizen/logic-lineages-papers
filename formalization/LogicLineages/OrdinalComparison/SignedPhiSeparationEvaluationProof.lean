module
public import LogicLineages.OrdinalComparison.SignedPhiSeparationDomainProof
public import LogicLineages.OrdinalComparison.SignedShiftCollectionGreatestProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SignedPhiSeparation.Proof
open SignedShiftCollection

/-- Apply the accepted literal natural-evaluator collection identity at the
exact rebased input. No occurrence is dropped in the original value. -/
theorem evaluation_collected (row : Row) (x : Nat) :
    value row (shiftedInput row x) =
      CommonHeadCollectedRow.weighted
        (fun k => (Phi (rebasedInput row x + k) : Int)) (collected row) := by
  have hd := domainOffset_le_delta row
  have he : (rebasedInput row x : Int) + (domainOffset row : Int) =
      (shiftedInput row x : Int) := by
    unfold rebasedInput shiftedInput
    omega
  symm
  rw [SignedShiftCollection.Proof.natural_weighted_collected row
    (fun k => (Phi k : Int)) (rebasedInput row x)]
  simp only [SignedShiftCollection.weighted, value, argument, he]

private theorem weighted_leading_lower (r : CommonHeadLargeRow.Row)
    (f : Nat → Int) (lead : Int × Nat)
    (hp : r.Pairwise (fun a b => a.2 ≠ b.2)) (hm : lead ∈ r)
    (hu : ∀ a ∈ r, a.2 ≤ lead.2) :
    CommonHeadCollectedRow.weighted f r = lead.1 * f lead.2 +
      CommonHeadCollectedRow.weighted f (r.filter (fun a => decide (a.2 < lead.2))) := by
  induction r with
  | nil => simp at hm
  | cons a r ih =>
    obtain ⟨ha, hp⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hm with he | hm
    · subst a
      have hf : r.filter (fun b => decide (b.2 < lead.2)) = r := by
        apply List.filter_eq_self.mpr
        intro b hb
        have hle := hu b (List.mem_cons_of_mem lead hb)
        have hne := ha b hb
        have hlt : b.2 < lead.2 := by omega
        simpa only [decide_eq_true_eq] using hlt
      simp [CommonHeadCollectedRow.weighted, hf]
    · have hlt : a.2 < lead.2 := by
        have hle := hu a List.mem_cons_self
        have hne := ha lead hm
        omega
      have hi := ih hp hm (fun b hb => hu b (List.mem_cons_of_mem a hb))
      have hf : (a :: r).filter (fun b => decide (b.2 < lead.2)) =
          a :: r.filter (fun b => decide (b.2 < lead.2)) := by
        simp only [List.filter_cons, hlt, decide_true, if_true]
      change a.1 * f a.2 + CommonHeadCollectedRow.weighted f r = _
      rw [hf]
      change a.1 * f a.2 + CommonHeadCollectedRow.weighted f r =
        lead.1 * f lead.2 +
          (a.1 * f a.2 + CommonHeadCollectedRow.weighted f
            (r.filter (fun b => decide (b.2 < lead.2))))
      rw [hi]
      omega

theorem evaluation_of_cancelled (row : Row) (h : collected row = []) (x : Nat) :
    value row (shiftedInput row x) = 0 := by
  rw [evaluation_collected, h]
  rfl

/-- The leader is the actual surviving greatest block; every remaining term
is precisely one of the strictly lower collected blocks defining A. -/
theorem evaluation_leading_lower (row : Row) (h : collected row ≠ []) (x : Nat) :
    value row (shiftedInput row x) =
      leadingCoefficient row *
        (Phi (argument (shiftedInput row x) (greatestShift row)) : Int) +
      CommonHeadCollectedRow.weighted
        (fun k => (Phi (rebasedInput row x + k) : Int)) (lowerRow row) := by
  have hd := (SignedShiftCollection.Proof.exactCollectionAndSupport row).2.2.1
  have hg := SignedShiftCollection.Proof.actualGreatestSurvivingShift row h
  rw [evaluation_collected, greatestArgument_rebased]
  exact weighted_leading_lower (collected row)
    (fun k => (Phi (rebasedInput row x + k) : Int))
    (leadingCoefficient row, greatestKey row) hd hg.1 hg.2.2.1

theorem exactEvaluationAndCancellation : Targets.ExactEvaluationAndCancellation := by
  intro row
  exact ⟨evaluation_collected row, evaluation_of_cancelled row, evaluation_leading_lower row⟩

end LogicLineages.OrdinalComparison.SignedPhiSeparation.Proof
