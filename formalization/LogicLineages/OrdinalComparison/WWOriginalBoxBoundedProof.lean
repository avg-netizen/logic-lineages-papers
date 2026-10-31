module
public import LogicLineages.OrdinalComparison.WWOriginalBoxBoundedTargets
public import LogicLineages.OrdinalComparison.WWOriginalBoxPositiveProof
public import LogicLineages.OrdinalComparison.WWOriginalInfiniteCollapseProof
public import LogicLineages.OrdinalComparison.WWOriginalOmegaProductProof
public import LogicLineages.OrdinalComparison.WWOriginalBoundedDeltaProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open AdmissibleSum AdmissibleAssignment AdmissiblePartial
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

private theorem expand_ambient {Γ : List Ty} {n i : Nat} (s : Shape n)
    (xs : Fin n → OrdinalExpression Γ) (h : ∀ j, AmbientGrade Γ i (xs j)) :
    AmbientGrade Γ i (expand s xs) := by
  induction s with
  | leaf => exact h 0
  | @join n m a b iha ihb =>
    exact .add (iha _ (fun j => h (Fin.castAdd m j)))
      (ihb _ (fun j => h (Fin.natAdd n j)))

private theorem three_ambient {Γ : List Ty} {i : Nat} (p : Policy) (site : MacroSite)
    {a b c : OrdinalExpression Γ} (ha : AmbientGrade Γ i a)
    (hb : AmbientGrade Γ i b) (hc : AmbientGrade Γ i c) :
    AmbientGrade Γ i (three p site a b c) := by
  apply expand_ambient
  intro j
  split
  · exact ha
  · split
    · exact hb
    · exact hc

private theorem one_norm {Γ : List Ty} (ρ : AdmissibleSubstitution Γ) :
    actualOrdinalNorm (expressionValue ρ .one) = 1 := by
  simpa [expressionValue, denote] using (finiteNorm 1).2

private theorem add_norm {Γ : List Ty} (ρ : AdmissibleSubstitution Γ) (f g : OrdinalExpression Γ) :
    actualOrdinalNorm (expressionValue ρ (.add f g)) =
      actualOrdinalNorm (expressionValue ρ f) + actualOrdinalNorm (expressionValue ρ g) :=
  actualNaturalSumNormAdditivity _ _ (originalExpressionValueBelowEpsilonZero Γ ρ f)
    (originalExpressionValueBelowEpsilonZero Γ ρ g)

private theorem three_norm {Γ : List Ty} (ρ : AdmissibleSubstitution Γ) (p : Policy)
    (site : MacroSite) (a b c : OrdinalExpression Γ) :
    actualOrdinalNorm (expressionValue ρ (three p site a b c)) =
      actualOrdinalNorm (expressionValue ρ a) + actualOrdinalNorm (expressionValue ρ b) +
        actualOrdinalNorm (expressionValue ρ c) := by
  unfold three
  rw [originalShapeNormAdditivity]
  simp [List.ofFn_succ, Nat.add_assoc]

theorem originalBoxTailGradeAndNorm : Targets.OriginalBoxTailGradeAndNorm := by
  intro Γ p n f g hf hg
  by_cases hn : n = 0
  · subst n
    simp only [boxTail, if_pos rfl, Nat.add_zero]
    exact ⟨.add hf hg, fun ρ => add_norm ρ f g⟩
  · have hnum : AmbientGrade Γ 0 (numeral p n) := by
      cases n with
      | zero => contradiction
      | succ n => exact expand_ambient _ _ (fun _ => .one 0)
    rw [boxTail, if_neg hn]
    refine ⟨three_ambient p .optionalBoxTail hf hg hnum, ?_⟩
    intro ρ
    rw [three_norm, numeral, originalPositiveRepeatNorm Γ ρ p .numeral n .one (by omega), one_norm]
    simp

private theorem product_below {a b : Ordinal} (ha : a < epsilonZero) (hb : b < epsilonZero) :
    ordinalNaturalProduct a b < epsilonZero := by
  obtain ⟨x, hx⟩ := normalRepresentationComplete a ha
  obtain ⟨y, hy⟩ := normalRepresentationComplete b hb
  rw [← hx, ← hy, ← naturalProductDenotation x y]
  exact normalRepresentationSound (naturalProduct x y)

private theorem collapse_control {Γ : List Ty} (ρ : AdmissibleSubstitution Γ)
    (h t : OrdinalExpression Γ) (hh : AmbientGrade Γ 1 h) (ht : AmbientGrade Γ 0 t) :
    fastControl 2 (actualOrdinalNorm (expressionValue ρ t)) ≤
      actualOrdinalNorm (expressionValue ρ (.collapse h t)) := by
  obtain ⟨k, hk⟩ := originalAmbientScalarFinite Γ t ht ρ
  let a := ordinalNaturalProduct Ordinal.omega0 (expressionValue ρ h)
  have hae : a < epsilonZero := product_below
    (originalClosedValueBelowEpsilonZero .omega) (originalExpressionValueBelowEpsilonZero Γ ρ h)
  have hai : Ordinal.omega0 ≤ a := actualOmegaNaturalProductInfinite _
    (originalAmbientGradePositive Γ 1 h hh ρ) (originalExpressionValueBelowEpsilonZero Γ ρ h)
  have he := actualFiniteTailClosureNorm a hae k
  have hi : Ordinal.omega0 ≤ a + (k : Ordinal) := hai.trans le_self_add
  have hc := actualInfiniteCollapseControlLower (a + (k : Ordinal)) hi he.1
  have hkn : k ≤ actualOrdinalNorm (a + (k : Ordinal)) := by rw [he.2]; omega
  have hb : fastControl 2 k ≤ Phi (actualOrdinalNorm (a + (k : Ordinal))) := by
    apply ((fastControl_strictMono 2).monotone hkn).trans
    exact ((fastControl_level_mono _) (show 2 ≤ 5 by decide)).trans
      ((fastControl_strictMono 5).monotone (Nat.le_add_right _ 100))
  rw [hk, (finiteNorm k).2]
  change _ ≤ actualOrdinalNorm ((actualCollapse
    (ordinalNaturalSum a (expressionValue ρ t)) : Nat) : Ordinal)
  rw [hk, actualNaturalSumFiniteRight, (finiteNorm _).2]
  exact hb.trans (Nat.le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self _) hc))

theorem originalSourceBoxBounded : Targets.OriginalSourceBoxBounded := by
  intro Γ m n hnm p f g gf gg bf bg
  have bf' := (originalBoundedVectorSupportBridge Γ m f).mpr bf
  have bg' := (originalBoundedVectorSupportBridge Γ n g).mpr bg
  let h := ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) 1
  let t := boxTail p n (f 0) (g 0)
  have gh : AmbientGrade Γ 1 h := originalBoxPositiveGrade Γ m n hnm f g gf gg 1 (by omega) (by omega)
  have gt : AmbientGrade Γ 0 t := (originalBoxTailGradeAndNorm Γ p n (f 0) (g 0) (gf 0) (gg 0)).1
  have hbound (ρ : AdmissibleSubstitution Γ) (i : Nat) (hi : 0 < i) (him : i ≤ m) :
      actualOrdinalNorm (expressionValue ρ
        (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) i)) ≤
      fastControl 2 (actualOrdinalNorm (expressionValue ρ t)) := by
    have ht := (originalBoxTailGradeAndNorm Γ p n (f 0) (g 0) (gf 0) (gg 0)).2 ρ
    rw [ht]
    apply originalBoxPositiveNorm Γ m n hnm f g ρ _ _ ?_ (bf' ρ) (bg' ρ) i hi him
    have hp := actualPositiveOrdinalNorm _ (originalAmbientGradePositive Γ 0 (f 0) (gf 0) ρ)
      (originalExpressionValueBelowEpsilonZero Γ ρ (f 0))
    omega
  have hn : CollapseNormPremise h t := by
    intro ρ
    rw [← originalScalarValueNorm Γ ρ t gt]
    exact hbound ρ 1 (by omega) (by omega)
  constructor
  · intro j
    rw [box]
    split
    · rename_i hj
      rw [hj]
      exact .collapse gh gt hn
    · rename_i hj
      exact originalBoxPositiveGrade Γ m n hnm f g gf gg j.val (by omega) (by have := j.isLt; omega)
  · apply (originalBoundedVectorSupportBridge Γ m _).mp
    intro ρ j
    have h0 : box p f g 0 = .collapse h t := by simp [box, h, t]
    rw [h0]
    by_cases hj : j.val = 0
    · have he : j = 0 := Fin.ext hj
      subst j
      rw [h0]
    · rw [box, if_neg hj]
      exact (hbound ρ j.val (by omega) (by have := j.isLt; omega)).trans
        (collapse_control ρ h t gh gt)

end LogicLineages.OrdinalComparison.Source.OriginalDomain
