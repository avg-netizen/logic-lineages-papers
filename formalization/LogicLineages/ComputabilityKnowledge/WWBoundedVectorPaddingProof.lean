module

public import LogicLineages.ComputabilityKnowledge.Comparators.WWBoundedVectorPadding
public import LogicLineages.ComputabilityKnowledge.WWGroundClassesProof
public import LogicLineages.ComputabilityKnowledge.WWFiniteEnvelopeProof
public import LogicLineages.ComputabilityKnowledge.WWOmegaFiniteCalibrationProof

@[expose] public section

/-! Literal original bounded-vector padding, after independent exact target
freeze. These are the two specified semantic reductions, not a claim of MRDP
or of general finite-O decision effectiveness. -/
namespace LogicLineages.ComputabilityKnowledge.WWBoundedVectorPaddingProof

open PositiveExpression WWOrdinalTermSemantics WWClosedAssignment WWGroundAdmissibility WWGroundClasses
open WWBoundedVectorPadding
open LogicLineages.OrdinalComparison

private theorem substituted_value {d : Nat} (t : Term (Fin d)) (χ : Fin d → Term Empty)
    (ρ : Fin d → PosNat)
    (h : ∀ i ∈ support t, closedValue (χ i) = ((ρ i : Nat) : Ordinal.{0})) :
    closedValue (substitute χ t) = denote (fun i => ((ρ i : Nat) : Ordinal)) t := by
  unfold closedValue
  rw [WWOrdinalTermSemanticsProof.structuralSubstitution]
  exact WWGroundAdmissibilityProof.originalLocality d t _ _ h

private theorem relation_transport {d : Nat} (a b : Term (Fin d)) (r : Ordinal.{0} → Ordinal.{0} → Prop) :
    (∀ χ : Fin d → Term Empty, Admissible (support a ∪ support b) χ →
      r (closedValue (substitute χ a)) (closedValue (substitute χ b))) ↔
    ∀ ρ : Fin d → PosNat, r (denote (fun i => ((ρ i : Nat) : Ordinal)) a)
      (denote (fun i => ((ρ i : Nat) : Ordinal)) b) := by
  constructor
  · intro h ρ
    obtain ⟨χ, hχ, hρ⟩ := WWGroundAdmissibilityProof.exactPositiveTuples.2 d ρ
    have hh := h χ (fun i hi => hχ i (Finset.mem_univ i))
    rw [substituted_value a χ ρ (fun i hi => hρ i),
      substituted_value b χ ρ (fun i hi => hρ i)] at hh
    exact hh
  · intro h χ hχ
    obtain ⟨ρ, hρ⟩ := WWGroundAdmissibilityProof.exactPositiveTuples.1 d _ χ hχ
    rw [substituted_value a χ ρ (fun i hi => hρ i (Finset.mem_union_left _ hi)),
      substituted_value b χ ρ (fun i hi => hρ i (Finset.mem_union_right _ hi))]
    exact h ρ

private theorem comparison_pointwise {d : Nat} (weak : Bool) (a b : Term (Fin d)) :
    Comparison weak a b ↔ ∀ ρ : Fin d → PosNat,
      if weak then denote (fun i => ((ρ i : Nat) : Ordinal)) a ≤ denote (fun i => ((ρ i : Nat) : Ordinal)) b
      else denote (fun i => ((ρ i : Nat) : Ordinal)) a < denote (fun i => ((ρ i : Nat) : Ordinal)) b :=
  relation_transport a b (fun x y => if weak then x ≤ y else x < y)

private theorem norm_pointwise {d : Nat} (a b : Term (Fin d)) :
    NormComparison true a b ↔ ∀ ρ : Fin d → PosNat,
      actualOrdinalNorm (denote (fun i => ((ρ i : Nat) : Ordinal)) a) ≤
        actualOrdinalNorm (denote (fun i => ((ρ i : Nat) : Ordinal)) b) := by
  simpa only [NormComparison, ↓reduceIte] using
    relation_transport a b (fun x y => actualOrdinalNorm x ≤ actualOrdinalNorm y)

private theorem embed_value {d : Nat} (e : Expr (Fin d)) (ρ : Fin d → PosNat) :
    denote (fun i => ((ρ i : Nat) : Ordinal)) (embed e) = (e.eval ρ : Ordinal) :=
  (WWOrdinalTermSemanticsProof.literalEmbedding d e ρ).1

private theorem norm_nat (n : Nat) : actualOrdinalNorm (n : Ordinal.{0}) = n :=
  (WWOrdinalTermSemanticsProof.finiteNorm n).2

private noncomputable def headNumber {d : Nat} (u v : Expr (Fin d)) (ρ : Fin d → PosNat) : Nat :=
  actualCollapse (WWOmegaFiniteCalibration.block ((remainder u v).eval ρ) ((control u v).eval ρ))

private theorem head_value {d : Nat} (u v : Expr (Fin d)) (ρ : Fin d → PosNat) :
    denote (fun i => ((ρ i : Nat) : Ordinal)) (head u v) = (headNumber u v ρ : Ordinal) := by
  simp only [head, denote, embed_value]
  rfl

private theorem head_add_one_value {d : Nat} (u v : Expr (Fin d)) (ρ : Fin d → PosNat) :
    denote (fun i => ((ρ i : Nat) : Ordinal)) (.add (head u v) .one) = ((headNumber u v ρ + 1 : Nat) : Ordinal) := by
  change ordinalNaturalSum (denote _ (head u v)) 1 = _
  rw [head_value]
  simpa only [Nat.cast_one] using WWOrdinalTermSemanticsProof.naturalSum_finite (headNumber u v ρ) 1

private theorem head_dominates {d : Nat} (u v : Expr (Fin d)) (ρ : Fin d → PosNat) :
    (remainder u v).eval ρ ≤ headNumber u v ρ :=
  (WWOmegaFiniteCalibrationProof.collapseCalibration _ _).2

private theorem remainder_depth {d : Nat} (u v : Expr (Fin d)) (hu : u.depth ≤ 2) (hv : v.depth ≤ 2) :
    (remainder u v).depth ≤ 2 := by
  simp only [remainder, Expr.depth, max_le_iff]
  exact ⟨⟨hu, hv⟩, by omega⟩

theorem originalHead : Comparators.WWBoundedVectorPadding.OriginalHead := by
  intro d u v hu hv
  have hR := remainder_depth u v hu hv
  have hC : C d 0 (head u v) := by
    refine C.collapse (WWGroundClassesProof.exponentialFragmentMembership d _ 1 (by omega))
      (WWGroundClassesProof.additiveFragmentMembership d _ (WWFiniteEnvelopeProof.literalEnvelope d _).2) ?_
    intro χ hχ
    obtain ⟨ρ, hρ⟩ := WWGroundAdmissibilityProof.exactPositiveTuples.1 d _ χ hχ
    have hr := substituted_value (embed (remainder u v)) χ ρ (fun i hi => hρ i (Finset.mem_union_left _ hi))
    have hg := substituted_value (embed (control u v)) χ ρ (fun i hi => hρ i (Finset.mem_union_right _ hi))
    rw [hr, hg, embed_value, embed_value, norm_nat, Ordinal.card_nat, Cardinal.toNat_natCast]
    exact (WWFiniteEnvelopeProof.sharedPositiveControl d _ hR ρ).2
  refine ⟨hC, (norm_pointwise _ _).mpr ?_⟩
  intro ρ
  rw [embed_value, head_value, norm_nat, norm_nat]
  exact head_dominates u v ρ

private theorem c_pair {d : Nat} (a b : Term (Fin d)) (ha : C d 0 a) (hb : C d 1 b) : CVector [a,b] := by
  refine ⟨by simp, ?_⟩
  intro i hi
  cases i with
  | zero => exact ha
  | succ i =>
      cases i with
      | zero => exact hb
      | succ i => simp only [List.length_cons, List.length_nil] at hi; omega

private theorem bounded_pair {d : Nat} (a b : Term (Fin d))
    (hab : NormComparison true b a) : VectorBoundedNorm [a,b] := by
  intro i
  cases i with
  | zero => intro χ hχ; exact le_rfl
  | succ i =>
      cases i with
      | zero => exact hab
      | succ i =>
          apply (norm_pointwise _ _).mpr
          intro ρ
          change actualOrdinalNorm 0 ≤ _
          have hz : actualOrdinalNorm (0 : Ordinal.{0}) = 0 := by simpa only [Nat.cast_zero] using norm_nat 0
          rw [hz]
          exact Nat.zero_le _

theorem originalBoundedVectors : Comparators.WWBoundedVectorPadding.OriginalBoundedVectors := by
  intro d u v hu hv
  have hH := (originalHead d u v hu hv).1
  have hL : CVector (left u v) := c_pair _ _ hH
    (WWGroundClassesProof.exponentialFragmentMembership d _ 1 (by omega))
  have hW : CVector (weakRight u v) := c_pair _ _ hH
    (WWGroundClassesProof.exponentialFragmentMembership d _ 1 (by omega))
  have hS : CVector (strictRight u v) := c_pair _ _ (C.add hH (C.one 0))
    (WWGroundClassesProof.exponentialFragmentMembership d _ 1 (by omega))
  refine ⟨hL, hW, hS, bounded_pair _ _ ?_, bounded_pair _ _ ?_, bounded_pair _ _ ?_⟩
  · apply (norm_pointwise _ _).mpr
    intro ρ
    rw [embed_value, head_value, norm_nat, norm_nat]
    have h := head_dominates u v ρ
    simp only [remainder, eval_add, eval_one] at h ⊢
    omega
  · apply (norm_pointwise _ _).mpr
    intro ρ
    rw [embed_value, head_value, norm_nat, norm_nat]
    have h := head_dominates u v ρ
    simp only [remainder, eval_add, eval_one] at h
    omega
  · apply (norm_pointwise _ _).mpr
    intro ρ
    rw [embed_value, head_add_one_value, norm_nat, norm_nat]
    have h := head_dominates u v ρ
    simp only [remainder, eval_add, eval_one] at h
    omega

private theorem head_strict {d : Nat} (u v : Expr (Fin d)) :
    Comparison false (head u v) (.add (head u v) .one) := by
  apply (comparison_pointwise _ _ _).mpr
  intro ρ
  simp only [Bool.false_eq_true, ↓reduceIte, head_value, head_add_one_value, Nat.cast_lt]
  omega

theorem exactComparisonReduction : Comparators.WWBoundedVectorPadding.ExactComparisonReduction := by
  intro d u v hu hv
  have hc := WWGroundAdmissibilityProof.sourceComparisons d (.add v .one) u true
  simp only [eval_add, eval_one, ↓reduceIte] at hc
  constructor
  · constructor
    · intro h
      exact hc.mp (h 1)
    · intro h i
      have ht := hc.mpr h
      cases i with
      | zero => intro χ hχ; exact le_rfl
      | succ i =>
          cases i with
          | zero => exact ht
          | succ i => intro χ hχ; exact le_rfl
  · constructor
    · intro h
      exact hc.mp (h.2 1 (by omega))
    · intro h
      refine ⟨head_strict u v, ?_⟩
      intro i hi
      have ht := hc.mpr h
      cases i with
      | zero => omega
      | succ i =>
          cases i with
          | zero => exact ht
          | succ i => intro χ hχ; exact le_rfl

theorem wwBoundedVectorPadding : Comparators.WWBoundedVectorPadding.Target :=
  ⟨originalHead, originalBoundedVectors, exactComparisonReduction⟩

end LogicLineages.ComputabilityKnowledge.WWBoundedVectorPaddingProof
