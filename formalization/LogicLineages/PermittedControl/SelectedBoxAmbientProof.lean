module
public import LogicLineages.PermittedControl.SelectedBoxTailProof
public import LogicLineages.PermittedControl.SelectedBoundedDeltaProof
public import LogicLineages.OrdinalComparison.WWOriginalOmegaProductProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedBoxAmbientProof
open OrdinalComparison Source SelectedSourceDomain SelectedBoundedDelta
open Source.AdmissibleSum Source.AdmissibleAssignment Source.AdmissiblePartial
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

 theorem collapse_control (ctrl : Nat → Nat) (K : Nat) (hctrl : SelectedWithThreshold ctrl K)
    {Γ : List Ty} (ρ : AdmissibleSubstitution ctrl Γ) (h t : OrdinalExpression Γ)
    (hh : AmbientGrade ctrl Γ 1 h) (ht : AmbientGrade ctrl Γ 0 t) :
    fastControl 2 (actualOrdinalNorm (expressionValue ctrl ρ t)) ≤
      actualOrdinalNorm (expressionValue ctrl ρ (.collapse h t)) := by
  obtain ⟨k,hk⟩ := SelectedNormSumsProof.scalar_finite ctrl Γ t ht ρ
  let a := ordinalNaturalProduct Ordinal.omega0 (expressionValue ctrl ρ h)
  have hae : a < epsilonZero := SelectedValueClosureProof.product_below
    SelectedValueClosureProof.omega_below (SelectedValueClosureProof.ambient_below ctrl ρ h)
  have hai : Ordinal.omega0 ≤ a := Source.OriginalDomain.actualOmegaNaturalProductInfinite _
    (SelectedGradedPositivityProof.ambient_positive ctrl K hctrl hh ρ)
    (SelectedValueClosureProof.ambient_below ctrl ρ h)
  have he := actualFiniteTailClosureNorm a hae k
  have hi : Ordinal.omega0 ≤ a + (k : Ordinal) := hai.trans le_self_add
  have hc := (selectedCollapseEstimates ctrl (SelectedGradedPositivityProof.selected_forms hctrl)).2.2.2.2
    (a+(k : Ordinal)) he.1 hi
  have hkn : k ≤ actualOrdinalNorm (a+(k : Ordinal)) := by rw [he.2]; omega
  have hb : fastControl 2 k ≤ G (actualOrdinalNorm (a+(k : Ordinal))) := by
    apply ((fastControl_strictMono 2).monotone hkn).trans
    exact ((fastControl_level_mono _) (show 2 ≤ 5 by decide)).trans
      ((fastControl_strictMono 5).monotone (Nat.le_add_right _ 100))
  have hge := (selected_admissibility ctrl (SelectedGradedPositivityProof.selected_forms hctrl)).2
    (actualOrdinalNorm (a+(k : Ordinal)))
  rw [hk,(finiteNorm k).2]
  change _ ≤ actualOrdinalNorm ((ParametricActualCollapse.collapseWith ctrl
    (ordinalNaturalSum a (expressionValue ctrl ρ t)) : Nat) : Ordinal)
  rw [hk,actualNaturalSumFiniteRight,(finiteNorm _).2]
  exact hb.trans (hge.trans hc.le)

 theorem positiveBound (ctrl : Nat → Nat) (K : Nat) (hctrl : SelectedWithThreshold ctrl K)
    (Γ : List Ty) (m n : Nat) (hnm : n < m) (p : Policy)
    (f : OrdinalVector Γ m) (g : OrdinalVector Γ n)
    (gf : ∀ j, AmbientGrade ctrl Γ j.val (f j)) (gg : ∀ j, AmbientGrade ctrl Γ j.val (g j))
    (bf : SourceBoundedVector ctrl f) (bg : SourceBoundedVector ctrl g)
    (ρ : AdmissibleSubstitution ctrl Γ) (i : Nat) (hi : 0 < i) (him : i ≤ m) :
    actualOrdinalNorm (expressionValue ctrl ρ
      (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) i)) ≤
      fastControl 2 (actualOrdinalNorm (expressionValue ctrl ρ (boxTail p n (f 0) (g 0)))) := by
  have bf' := (SelectedBoundedDeltaProof.boundedVectorSupportBridge ctrl Γ m f).mpr bf
  have bg' := (SelectedBoundedDeltaProof.boundedVectorSupportBridge ctrl Γ n g).mpr bg
  have ht := (SelectedBoxTailProof.tailGradeAndNorm ctrl Γ p n (f 0) (g 0) (gf 0) (gg 0)).2 ρ
  rw [ht]
  apply SelectedBoxPositiveProof.positiveNorm ctrl Γ m n hnm f g ρ _ _ ?_ (bf' ρ) (bg' ρ) i hi him
  have hp := Source.OriginalDomain.actualPositiveOrdinalNorm _
    (SelectedGradedPositivityProof.ambient_positive ctrl K hctrl (gf 0) ρ)
    (SelectedValueClosureProof.ambient_below ctrl ρ (f 0))
  omega

 theorem boxGuard : SelectedBoxTargets.BoxGuard := by
  intro ctrl K hctrl Γ m n hnm p f g gf gg bf bg ρ
  have gt := (SelectedBoxTailProof.tailGradeAndNorm ctrl Γ p n (f 0) (g 0) (gf 0) (gg 0)).1
  rw [← SelectedNormSumsProof.scalarNorm ctrl Γ ρ _ gt]
  exact positiveBound ctrl K hctrl Γ m n hnm p f g gf gg bf bg ρ 1 (by omega) (by omega)

 theorem ambientBox : SelectedBoxTargets.AmbientBox := by
  intro ctrl K hctrl Γ m n hnm p f g gf gg bf bg
  let h := ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) 1
  let t := boxTail p n (f 0) (g 0)
  have gh : AmbientGrade ctrl Γ 1 h := SelectedBoxPositiveProof.positiveGrade ctrl Γ m n hnm f g gf gg 1 (by omega) (by omega)
  have gt : AmbientGrade ctrl Γ 0 t := (SelectedBoxTailProof.tailGradeAndNorm ctrl Γ p n (f 0) (g 0) (gf 0) (gg 0)).1
  have hn : CollapseNormPremise ctrl h t := boxGuard ctrl K hctrl Γ m n hnm p f g gf gg bf bg
  constructor
  · intro j
    rw [box]
    split
    · rename_i hj
      rw [hj]
      exact .collapse gh gt hn
    · rename_i hj
      exact SelectedBoxPositiveProof.positiveGrade ctrl Γ m n hnm f g gf gg j.val (by omega) (by have := j.isLt; omega)
  · apply (SelectedBoundedDeltaProof.boundedVectorSupportBridge ctrl Γ m _).mp
    intro ρ j
    have h0 : box p f g 0 = .collapse h t := by simp [box,h,t]
    rw [h0]
    by_cases hj : j.val = 0
    · have he : j = 0 := Fin.ext hj
      subst j
      rw [h0]
    · rw [box,if_neg hj]
      exact (positiveBound ctrl K hctrl Γ m n hnm p f g gf gg bf bg ρ j.val
        (by omega) (by have := j.isLt; omega)).trans (collapse_control ctrl K hctrl ρ h t gh gt)

end LogicLineages.PermittedControl.SelectedBoxAmbientProof
