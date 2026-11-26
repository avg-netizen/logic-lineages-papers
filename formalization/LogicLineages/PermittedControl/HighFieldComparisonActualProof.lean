module
public import LogicLineages.PermittedControl.HighFieldComparisonTargets
import LogicLineages.PermittedControl.HighFieldComparisonCalibrationProof
import LogicLineages.PermittedControl.ShortFieldNormalizationProof
import LogicLineages.PermittedControl.LongFieldDistinctBoundProof
import LogicLineages.PermittedControl.LongFieldSameBoundProof
import LogicLineages.PermittedControl.FieldComparisonProof
import LogicLineages.PermittedControl.ThresholdNumericCalibrationProof

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison

private theorem sorted_form_at_actual_values (f : Nat → Nat) (F G : ValueField)
    (hF : LongField F) (hG : LongField G) (lo hi vLo vHi : Nat)
    (ha : FormHolds f (distinctForm F G) lo hi vLo vHi) :
    RawSortedFormHolds f (encodeComparisonForm (distinctForm F G)) lo hi vLo vHi := by
  cases hc : distinctForm F G with
  | const c =>
    rw [hc] at ha
    exact Or.inl ⟨c,rfl,ha⟩
  | linear sign H =>
    have hshape := formWellFormed F G hF hG sign H hc
    rw [hc] at ha
    obtain ⟨h,hv,hrows⟩ := ha
    exact Or.inr ⟨sign,H,h,rfl,hshape.1,hshape.2,hv,hrows⟩

theorem highFieldComparisonActual : HighFieldComparisonActual := by
  intro f B hf F G hF hG x y hBound
  let F' := normalizeShortField F
  let G' := normalizeShortField G
  have hF' : LongField F' := shortFieldNormalization.2.2.1 F hF
  have hG' : LongField G' := shortFieldNormalization.2.2.1 G hG
  rw [highFieldComparisonCalibration.2.2.1 B F G] at hBound
  change max (max (shortFieldTail B F) (shortFieldTail B G))
    (max (longFieldSameBound B F' G')
      (max (longFieldDistinctBound B F' G') (longFieldDistinctBound B G' F'))) ≤ min x y at hBound
  have hShort : max (shortFieldTail B F) (shortFieldTail B G) ≤ min x y :=
    (le_max_left _ _).trans hBound
  have hCmp : max (longFieldSameBound B F' G')
      (max (longFieldDistinctBound B F' G') (longFieldDistinctBound B G' F')) ≤ min x y :=
    (le_max_right _ _).trans hBound
  have hSame : longFieldSameBound B F' G' ≤ x :=
    ((le_max_left _ _).trans hCmp).trans (min_le_left _ _)
  have hDist : max (longFieldDistinctBound B F' G') (longFieldDistinctBound B G' F') ≤ min x y :=
    (le_max_right _ _).trans hCmp
  have hForward : longFieldDistinctBound B F' G' ≤ x :=
    ((le_max_left _ _).trans hDist).trans (min_le_left _ _)
  have hBackward : longFieldDistinctBound B G' F' ≤ y :=
    ((le_max_right _ _).trans hDist).trans (min_le_right _ _)
  have hShortF : shortFieldTail B F ≤ x := ((le_max_left _ _).trans hShort).trans (min_le_left _ _)
  have hShortG : shortFieldTail B G ≤ y := ((le_max_right _ _).trans hShort).trans (min_le_right _ _)
  have hOrig (vF vG : Nat) (hvF : FieldValue f F' x vF) (hvG : FieldValue f G' y vG) :
      FieldValue f F x vF ∧ FieldValue f G y vG ∧
      (∀ u v : Nat, FieldValue f F x u → FieldValue f G y v → u = vF ∧ v = vG) := by
    have hvF' := (shortFieldNormalization.2.2.2 f B hf F hF x vF hShortF).mpr hvF
    have hvG' := (shortFieldNormalization.2.2.2 f B hf G hG y vG hShortG).mpr hvG
    exact ⟨hvF',hvG',fun u v hu hv =>
      ⟨fieldValueUnique f F x u vF hu hvF',fieldValueUnique f G y v vG hv hvG'⟩⟩
  have hC := highFieldComparisonCalibration.2.2.2 F G x y
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · obtain ⟨vF,vG,hvF,hvG,hform⟩ := longFieldDistinctAtBound f B hf F' G' hF' hG' x y hForward hxy
    obtain ⟨hvF',hvG',hu⟩ := hOrig vF vG hvF hvG
    refine ⟨vF,vG,hvF',hvG',hu,?_,?_,?_⟩
    · intro _
      rw [hC.1 hxy]
      exact ⟨rfl,sorted_form_at_actual_values f F' G' hF' hG' x y vF vG hform⟩
    · intro he
      exact (ne_of_lt hxy he).elim
    · intro h
      exact (Nat.not_lt_of_ge hxy.le h).elim
  · subst y
    obtain ⟨vF,vG,hvF,hvG,hform⟩ := longFieldSameAtBound f B hf F' G' hF' hG' x hSame
    obtain ⟨hvF',hvG',hu⟩ := hOrig vF vG hvF hvG
    refine ⟨vF,vG,hvF',hvG',hu,?_,?_,?_⟩
    · intro h
      exact (Nat.lt_irrefl _ h).elim
    · intro he
      rw [hC.2.1 he,hform]
    · intro h
      exact (Nat.lt_irrefl _ h).elim
  · obtain ⟨vG,vF,hvG,hvF,hform⟩ := longFieldDistinctAtBound f B hf G' F' hG' hF' y x hBackward hyx
    obtain ⟨hvF',hvG',hu⟩ := hOrig vF vG hvF hvG
    refine ⟨vF,vG,hvF',hvG',hu,?_,?_,?_⟩
    · intro h
      exact (Nat.not_lt_of_ge hyx.le h).elim
    · intro he
      exact (ne_of_gt hyx he).elim
    · intro _
      rw [hC.2.2 hyx]
      refine ⟨rfl,sorted_form_at_actual_values f G' F' hG' hF' y x vG vF hform,?_⟩
      simpa only [flipHighComparisonAnswer,one_ne_zero,ite_false] using reverseComparisonCode_correct vG vF

end LogicLineages.PermittedControl.FieldComparison
