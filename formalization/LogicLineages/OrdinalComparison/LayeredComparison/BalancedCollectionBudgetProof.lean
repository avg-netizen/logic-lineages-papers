module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedCollectionAlgebraProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.Collection.Proof

private theorem collection_member_le_maximum {xs : List Nat} {x : Nat}
    (hx : x ∈ xs) : x ≤ maximum xs := by
  induction xs with
  | nil => cases hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst x
      exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

private theorem collection_maximum_le {xs : List Nat} {N : Nat}
    (h : ∀ x ∈ xs, x ≤ N) : maximum xs ≤ N := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons a xs ih =>
    exact max_le (h a List.mem_cons_self)
      (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

private theorem collection_maximum_mono {xs ys : List Nat}
    (h : ∀ x ∈ xs, x ∈ ys) : maximum xs ≤ maximum ys := by
  exact collection_maximum_le (fun x hx => collection_member_le_maximum (h x hx))

/-- Each threshold parameter is monotone in the literal printed formula. -/
private theorem collection_threshold_mono (K : Int)
    {C' C C0' C0 A' A B' B N' N : Nat}
    (hC : C' ≤ C) (hC0 : C0' ≤ C0) (hA : A' ≤ A)
    (hB : B' ≤ B) (hN : N' ≤ N) :
    BalancedNumerical.threshold K C' C0' A' B' N' ≤
      BalancedNumerical.threshold K C C0 A B N := by
  unfold BalancedNumerical.threshold
  exact max_le_max le_rfl
    (max_le_max (Nat.mul_le_mul_left 2 hC)
      (max_le_max
        (Nat.add_le_add_right
          (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hC0) (4 * K.natAbs)) 4)
        (max_le_max (Nat.add_le_add_right (Nat.add_le_add hA hB) 2)
          (Nat.add_le_add_right hN 2))))

/-- The representatives are literal original atoms, so cancellation cannot
increase any multiplier, complete-offset, or actual-head-norm maximum. -/
theorem collected_maxima_le (basis : List Nat) (row : Row) :
    multiplierMaximum (collect basis row) ≤ multiplierMaximum row ∧
    offsetMaximum (collect basis row) ≤ offsetMaximum row ∧
    normMaximum (collect basis row) ≤ normMaximum row := by
  have provenance : ∀ a ∈ (collect basis row).atoms,
      ∃ q : Int, (q, a.2) ∈ row.atoms := by
    intro a ha
    exact ((literalCollectedSupport basis row).2.1 a ha).2.2
  have hA : maximum ((collect basis row).atoms.flatMap (fun a => a.2.coefficients)) ≤
      maximum (row.atoms.flatMap (fun a => a.2.coefficients)) := by
    apply collection_maximum_mono
    intro c hc
    rcases List.mem_flatMap.mp hc with ⟨a, ha, hca⟩
    rcases provenance a ha with ⟨q, hq⟩
    exact List.mem_flatMap.mpr ⟨(q, a.2), hq, hca⟩
  have hB : offsetMaximum (collect basis row) ≤ offsetMaximum row := by
    apply collection_maximum_mono
    intro n hn
    rcases List.mem_map.mp hn with ⟨a, ha, hna⟩
    rcases provenance a ha with ⟨q, hq⟩
    exact List.mem_map.mpr ⟨(q, a.2), hq, hna⟩
  have hN : normMaximum (collect basis row) ≤ normMaximum row := by
    apply collection_maximum_mono
    intro n hn
    rcases List.mem_map.mp hn with ⟨a, ha, hna⟩
    rcases provenance a ha with ⟨q, hq⟩
    exact List.mem_map.mpr ⟨(q, a.2), hq, hna⟩
  exact ⟨max_le_max le_rfl hA, hB, hN⟩

/-- The entire outside remainder is retained and the original threshold is
still sufficient, including when every signed block cancels. -/
theorem originalThresholdBudget : Targets.OriginalThresholdBudget := by
  intro basis row
  have hC := coefficientMass_collect_le basis row
  have hOutside : outsideMaximum (collect basis row) = outsideMaximum row := rfl
  have hMax := collected_maxima_le basis row
  refine ⟨hC, hOutside, hMax.1, hMax.2.1, hMax.2.2, ?_⟩
  exact collection_threshold_mono row.constant hC hOutside.le
    hMax.1 hMax.2.1 hMax.2.2

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.Collection.Proof
