module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodeSupportProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodeCalibrationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
  NumberedStepContexts NumberedTypedFocus NumberedFocusCode NumberedFocusCodeSupportProof

theorem focusCalibration : NumberedFocusCodeTargets.ActualFocusCalibration := by
  intro n arity path
  induction path with
  | nil => intro Gamma tau q; simp [focusCode_nil, focus]
  | cons position path ih =>
    intro Gamma tau q
    cases position <;> cases q <;> try rfl
    case lam.lam =>
      simp only [focusCode_cons, termCode, descendCode, if_pos rfl, Option.bind_some,
        focus, Option.map_map, Function.comp_def]
      exact ih _ _ _
    case appFunction.app =>
      simp only [focusCode_cons, termCode, descendCode, Option.bind_some,
        focus, Option.map_map, Function.comp_def]
      exact ih _ _ _
    case ordinaryBase.ordinary index head base =>
      have h := argumentFocusValueCalibration path Gamma (fun tau q => ih Gamma tau q) index base
      unfold argumentFocusValue at h
      simpa only [focusCode_cons, termCode, descendCode, focus, Option.map_map,
        Function.comp_def] using h
    case numberedBase.numbered index label head types base extras =>
      have h := argumentFocusValueCalibration path Gamma (fun tau q => ih Gamma tau q) index base
      unfold argumentFocusValue at h
      simpa only [focusCode_cons, termCode, descendCode, focus, Option.map_map,
        Function.comp_def] using h
    case numberedExtras.numbered index label head types base extras =>
      have h := argumentFocusValueCalibration path Gamma (fun tau q => ih Gamma tau q) index extras
      unfold argumentFocusValue at h
      simpa only [focusCode_cons, termCode, descendCode, focus, Option.map_map,
        Function.comp_def] using h
    all_goals simp [focusCode_cons, termCode, descendCode, focus]
    all_goals (unfold focus <;> rfl)

theorem replacementCalibration : NumberedFocusCodeTargets.ActualReplacementCalibration := by
  intro n arity path
  induction path with
  | nil =>
    intro Gamma tau q f replacement h
    simp only [focus, Option.some.injEq] at h
    cases h
    rfl
  | cons position path ih =>
    intro Gamma tau q f replacement h
    cases position <;> cases q <;>
      try simp only [focus, Option.map_eq_some_iff] at h
    all_goals try contradiction
    case lam.lam =>
      obtain ⟨child, hchild, rfl⟩ := h
      have hx := ih _ _ _ child replacement hchild
      simp only [plug, termCode, replaceCode_lam, hx, Option.map_some]
    case appFunction.app =>
      obtain ⟨child, hchild, rfl⟩ := h
      have hx := ih _ _ _ child replacement hchild
      simp only [plug, termCode, replaceCode_app, hx, Option.map_some]
    case ordinaryBase.ordinary =>
      obtain ⟨child, hchild, rfl⟩ := h
      have hx := argumentReplacementCalibration path ih _ _ child replacement hchild
      simp only [plug, termCode, replaceCode_ordinary, hx, Option.map_some]
    case numberedBase.numbered =>
      obtain ⟨child, hchild, rfl⟩ := h
      have hx := argumentReplacementCalibration path ih _ _ child replacement hchild
      simp only [plug, termCode, replaceCode_numberedBase, hx, Option.map_some]
    case numberedExtras.numbered =>
      obtain ⟨child, hchild, rfl⟩ := h
      have hx := argumentReplacementCalibration path ih _ _ child replacement hchild
      simp only [plug, termCode, replaceCode_numberedExtras, hx, Option.map_some]
    all_goals
      unfold focus at h
      contradiction

theorem replacementFailure : NumberedFocusCodeTargets.ActualReplacementFailure := by
  intro n arity path Gamma tau q replacement h
  have hf : focusCode path Gamma tau (termCode q) = none := by
    rw [focusCalibration, h]
    rfl
  cases ht : traceCode path (Gamma, tau, termCode q) with
  | none => simp [replaceCode, ht]
  | some result => simp [focusCode, ht] at hf

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodeCalibrationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodeCalibrationProof
