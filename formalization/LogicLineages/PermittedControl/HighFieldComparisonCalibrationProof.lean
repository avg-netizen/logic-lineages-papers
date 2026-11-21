module
public import LogicLineages.PermittedControl.HighFieldComparisonTargets
import LogicLineages.PermittedControl.LongFieldTailCalibrationProof
import LogicLineages.PermittedControl.RawFieldComparisonFormCalibrationProof

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

private theorem normalize_code_calibrated (F : ValueField) :
    normalizeHighFieldCode (longFieldCode F) = longFieldCode (normalizeShortField F) := by
  cases F with
  | iterate a => rfl
  | entry a lam mu =>
    simp only [normalizeHighFieldCode,longFieldCode,one_ne_zero,ite_false,normalizeShortField]
    cases shortIterateCode (rawNoteEncode lam.1) (rawNoteEncode mu.1) a <;> rfl

private theorem high_short_code_calibrated (B : Nat) (F : ValueField) :
    highShortBoundCode B (longFieldCode F) = shortFieldTail B F := by
  cases F <;> rfl

private theorem high_bound_code_calibrated (B : Nat) (F G : ValueField) :
    highFieldComparisonBoundCode B (longFieldCode F) (longFieldCode G) =
      highFieldComparisonBound B F G := by
  have hFG := longFieldTailCodes_calibrated B (normalizeShortField F) (normalizeShortField G)
  have hGF := longFieldTailCodes_calibrated B (normalizeShortField G) (normalizeShortField F)
  simp only [highFieldComparisonBoundCode,highFieldComparisonBound,
    normalize_code_calibrated,high_short_code_calibrated,hFG.1,hFG.2,hGF.1]

theorem highFieldComparisonCalibration : HighFieldComparisonCalibration := by
  refine ⟨normalize_code_calibrated,high_short_code_calibrated,high_bound_code_calibrated,?_⟩
  intro F G x y
  have hFG := rawFieldComparisonFormCalibration.2.2 (normalizeShortField F) (normalizeShortField G)
  have hGF := rawFieldComparisonFormCalibration.2.2 (normalizeShortField G) (normalizeShortField F)
  refine ⟨?_,?_,?_⟩
  · intro hxy
    simp only [highRawComparisonForm,normalize_code_calibrated,if_pos hxy,hFG.1]
  · intro hxy
    subst y
    simp only [highRawComparisonForm,normalize_code_calibrated,lt_irrefl,ite_false,hFG.2.2]
  · intro hyx
    simp only [highRawComparisonForm,normalize_code_calibrated,if_neg (Nat.not_lt_of_ge hyx.le),
      if_pos hyx,hGF.1]

end LogicLineages.PermittedControl.FieldComparison
