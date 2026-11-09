module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmSignItemProof
public import LogicLineages.OrdinalComparison.CommonHeadCollectedRowAlgebraProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainPhiDominanceGrowthProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
open PolynomialGraphCompletion Algorithm

/-- Semantic proof data only. The actual stage still enumerates numeric
labels from syntax and never evaluates these preimages to select a branch. -/
noncomputable def numericLeaderData (r : Row) (ν : Nat → Nat) : CommonHeadLargeRow.Row :=
  (active r).map (fun a => (a.1*(if isCounter a then 1 else 2),
    wordValue (preimage a) (ν a.2.1)))

noncomputable def atomCorrection (a : Item) (ν : Nat → Nat) : Int :=
  2*(wordValue a.2.2 (ν a.2.1) : Int) -
    (if isCounter a then 1 else 2)*(wordValue (leader a).2 (ν a.2.1) : Int)

noncomputable def rawLinearValue (r : Row) (ν : Nat → Nat) : Int :=
  ((linearPart r).map (fun a => a.1*(ν a.2.1 : Int))).sum

noncomputable def numericRemainder (r : Row) (ν : Nat → Nat) : Int :=
  2*RowValue r ν - CommonHeadCollectedRow.weighted (fun n => (Phi n : Int))
    (CommonHeadCollectedRow.collect (numericLeaderData r ν))

private theorem weighted_bound (xs : List Item) (f : Item → Int) (U : Nat)
    (hf : ∀ a ∈ xs, (f a).natAbs ≤ U) :
    ((xs.map (fun a => a.1*f a)).sum).natAbs ≤
      (xs.map (fun a => a.1.natAbs)).sum*U := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha := Nat.mul_le_mul_left a.1.natAbs (hf a (by simp))
      have ht := ih (fun b hb => hf b (by simp [hb]))
      have hadd := Int.natAbs_add_le (a.1*f a) ((xs.map (fun a => a.1*f a)).sum)
      simp only [Int.natAbs_mul] at hadd
      simp only [List.map_cons,List.sum_cons]
      nlinarith

theorem numericLeaderData_mass (r : Row) (ν : Nat → Nat) :
    CommonHeadLargeRow.mass (numericLeaderData r ν) ≤ 2*nonlinearMass r := by
  unfold numericLeaderData CommonHeadLargeRow.mass nonlinearMass
  simp only [List.map_map,Function.comp_def]
  generalize active r = xs
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha : (a.1*(if isCounter a then 1 else 2) : Int).natAbs ≤ 2*a.1.natAbs := by
        cases hc : isCounter a <;> simp [hc,Int.natAbs_mul] <;> omega
      simp only [List.map_cons,List.sum_cons]
      omega

theorem collectedLeaderData_mass (r : Row) (ν : Nat → Nat) :
    CommonHeadLargeRow.mass (CommonHeadCollectedRow.collect (numericLeaderData r ν)) ≤
      2*nonlinearMass r :=
  (CommonHeadCollectedRow.Proof.literalCollectedSupport (numericLeaderData r ν)).2.2.trans
    (numericLeaderData_mass r ν)

theorem collectedLeaderData_inputs (r : Row) (ν : Nat → Nat) (b : Int × Nat)
    (hb : b ∈ CommonHeadCollectedRow.collect (numericLeaderData r ν)) :
    ∃ a ∈ active r, wordValue (preimage a) (ν a.2.1) = b.2 := by
  have hs := (CommonHeadCollectedRow.Proof.literalCollectedSupport (numericLeaderData r ν)).2.1 b hb
  obtain ⟨c,hc,hcb⟩ := hs.2.2
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
  exact ⟨a,ha,hcb⟩

theorem numericRemainder_decomposition (D : Nat) (r : Row) (hD : RowAllowed D r)
    (ν : Nat → Nat) (ht : ∀ a ∈ active (canonicalRow r), sourceTail a ≤ ν a.2.1) :
    numericRemainder (canonicalRow r) ν = 2*(canonicalRow r).1 +
      2*rawLinearValue (canonicalRow r) ν +
        ((active (canonicalRow r)).map (fun a => a.1*atomCorrection a ν)).sum := by
  let current := canonicalRow r
  let value := fun a : Item => a.1*(wordValue a.2.2 (ν a.2.1) : Int)
  have hp := ((List.filter_append_perm (fun a : Item => a.2.2.isEmpty) current.2).map value).sum_eq
  have hlinear : ((linearPart current).map value).sum = rawLinearValue current ν := by
    change ((linearPart current).map value).sum =
      ((linearPart current).map (fun a => a.1*(ν a.2.1 : Int))).sum
    congr 1
    apply List.map_congr_left
    intro a ha
    have hw : a.2.2 = [] := by simpa using (List.mem_filter.mp ha).2
    simp [value,hw,wordValue]
  simp only [List.map_append,List.sum_append] at hp
  change ((linearPart current).map value).sum+((active current).map value).sum =
    (current.2.map value).sum at hp
  rw [hlinear] at hp
  have hleaders : CommonHeadCollectedRow.weighted (fun n => (Phi n : Int))
      (CommonHeadCollectedRow.collect (numericLeaderData current ν)) =
      ((active current).map (fun a =>
        a.1*(if isCounter a then 1 else 2)*(wordValue (leader a).2 (ν a.2.1) : Int))).sum := by
    rw [CommonHeadCollectedRow.Proof.exactWeightedCollection]
    simp only [CommonHeadCollectedRow.weighted,numericLeaderData,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro a ha
    rw [(preimage_facts D r a hD ha _ (ht a ha)).2.2]
  have hc : 2*((active current).map value).sum =
      ((active current).map (fun a =>
        a.1*(if isCounter a then 1 else 2)*(wordValue (leader a).2 (ν a.2.1) : Int))).sum +
      ((active current).map (fun a => a.1*atomCorrection a ν)).sum := by
    generalize active current = xs
    induction xs with
    | nil => simp
    | cons a xs ih =>
        simp only [List.map_cons,List.sum_cons,value,atomCorrection]
        simp only [value,atomCorrection] at ih
        nlinarith only [ih]
  simp only [numericRemainder]
  rw [hleaders]
  change 2*(current.1+(current.2.map value).sum)-_ = _
  linear_combination -2*hp+hc

theorem atomCorrection_bound (D : Nat) (r : Row) (a : Item) (hD : RowAllowed D r)
    (ha : a ∈ active (canonicalRow r)) (ν : Nat → Nat) (U : Nat)
    (ht : sourceTail a ≤ ν a.2.1) (hU : wordValue (preimage a) (ν a.2.1) ≤ U) :
    (atomCorrection a ν).natAbs ≤ 2*(U+1) := by
  by_cases hc : isCounter a = true
  · have hbound := counter_correction_bound D r a hD ha hc _ ht
    have hzero : 0 ≤ atomCorrection a ν := by simpa [atomCorrection,hc] using hbound.1
    have hupper : atomCorrection a ν ≤ (2*(U+1) : Nat) := by
      simp only [atomCorrection,hc,if_true,one_mul]
      have hu : (wordValue (preimage a) (ν a.2.1) : Int) ≤ (U : Int) := by exact_mod_cast hU
      have hcast : ((2*(U+1) : Nat) : Int) = 2*(U : Int)+2 := by omega
      rw [hcast]
      linarith [hbound.2]
    have hh : ((atomCorrection a ν).natAbs : Int) ≤ (2*(U+1) : Nat) := by
      rw [Int.natAbs_of_nonneg hzero]
      exact hupper
    exact_mod_cast hh
  · have heq : atomCorrection a ν = 0 := by
      have hlead : wordValue (leader a).2 (ν a.2.1) = wordValue a.2.2 (ν a.2.1) := by
        simp [leader,hc]
      simp [atomCorrection,hc,hlead]
    simp [heq]

/-- The actual doubled correction remainder has the affine bound required
by the already checked collected-Phi sign theorem. -/
theorem numericRemainder_bound (D : Nat) (r : Row) (hD : RowAllowed D r)
    (ν : Nat → Nat) (U : Nat)
    (ht : ∀ a ∈ active (canonicalRow r), sourceTail a ≤ ν a.2.1)
    (hU : ∀ a ∈ active (canonicalRow r), wordValue (preimage a) (ν a.2.1) ≤ U)
    (hraw : ∀ a ∈ linearPart (canonicalRow r), ν a.2.1 ≤ U+preimageOffset (canonicalRow r)) :
    (numericRemainder (canonicalRow r) ν).natAbs ≤
      (2*nonlinearMass (canonicalRow r)+2*linearMass (canonicalRow r))*U +
        (2*nonlinearMass (canonicalRow r)+
          2*linearMass (canonicalRow r)*preimageOffset (canonicalRow r)+2*(canonicalRow r).1.natAbs) := by
  let current := canonicalRow r
  have hc := weighted_bound (active current) (fun a => atomCorrection a ν) (2*(U+1))
    (fun a ha => atomCorrection_bound D r a hD ha ν U (ht a ha) (hU a ha))
  have hl := weighted_bound (linearPart current) (fun a => (ν a.2.1 : Int))
    (U+preimageOffset current) (fun a ha => by simpa using hraw a ha)
  change (((active current).map (fun a => a.1*atomCorrection a ν)).sum).natAbs ≤
    nonlinearMass current*(2*(U+1)) at hc
  change (rawLinearValue current ν).natAbs ≤ linearMass current*(U+preimageOffset current) at hl
  rw [numericRemainder_decomposition D r hD ν ht]
  have h1 := Int.natAbs_add_le (2*current.1) (2*rawLinearValue current ν)
  have h2 := Int.natAbs_add_le (2*current.1+2*rawLinearValue current ν)
    (((active current).map (fun a => a.1*atomCorrection a ν)).sum)
  simp only [Int.natAbs_mul,show (2 : Int).natAbs = 2 from rfl] at h1
  nlinarith

/-- Reuse the checked arbitrary finite collected-Phi sign theorem at the
actual current preimages and actual counter remainder. The only selected
block here is a proof witness; the runtime keeps its numeric label class. -/
theorem actual_collected_sign (D : Nat) (r : Row) (hD : RowAllowed D r)
    (ν : Nat → Nat) (chosen : Int × Nat)
    (hchosen : chosen ∈ CommonHeadCollectedRow.collect (numericLeaderData (canonicalRow r) ν))
    (ht : ∀ a ∈ active (canonicalRow r), sourceTail a ≤ ν a.2.1)
    (hU : ∀ a ∈ active (canonicalRow r), wordValue (preimage a) (ν a.2.1) ≤ chosen.2)
    (hraw : ∀ a ∈ linearPart (canonicalRow r),
      ν a.2.1 ≤ chosen.2+preimageOffset (canonicalRow r))
    (hpay : signPayment (canonicalRow r) ≤ chosen.2) :
    Int.sign (RowValue (canonicalRow r) ν) = Int.sign chosen.1 := by
  let current := canonicalRow r
  let rows := CommonHeadCollectedRow.collect (numericLeaderData current ν)
  let S := nonlinearMass current
  let A := linearMass current
  let M := preimageOffset current
  let B := current.1.natAbs
  have hsupport := CommonHeadCollectedRow.Proof.literalCollectedSupport (numericLeaderData current ν)
  have hmax : ∀ b ∈ rows, b.2 ≤ chosen.2 := by
    intro b hb
    obtain ⟨a,ha,hab⟩ := collectedLeaderData_inputs current ν b hb
    rw [← hab]
    exact hU a ha
  have hR : (numericRemainder current ν).natAbs ≤
      (2*S+2*A)*chosen.2+(2*S+2*A*M+2*B) :=
    numericRemainder_bound D r hD ν chosen.2 ht hU hraw
  have hthreshold : 2*S+(2*S+2*A)+(2*S+2*A*M+2*B)+1 ≤ chosen.2 := by
    change 64*(S+A+A*M+B+1) ≤ chosen.2 at hpay
    simp only [Nat.mul_assoc]
    omega
  have hs := LayeredComparison.SnyatkovCompletion.PlainPhiDominanceProof.collected_sign
    rows hsupport.1 (2*S) (2*S+2*A) (2*S+2*A*M+2*B) (numericRemainder current ν)
    (collectedLeaderData_mass current ν) chosen hchosen (hsupport.2.1 chosen hchosen).1
    hmax hR hthreshold
  simpa [numericRemainder,Int.sign_mul] using hs

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
