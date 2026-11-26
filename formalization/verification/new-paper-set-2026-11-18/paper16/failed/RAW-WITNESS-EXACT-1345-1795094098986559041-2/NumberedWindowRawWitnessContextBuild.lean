import LogicLineages.PersistentMarking.NumberedWindowRawWitnessRootBuild

namespace LogicLineages.PersistentMarking.NumberedWindowRawWitnessContextBuild
open Spine NumberedWindowSyntax NumberedWindowRules NumberedWindowLiteralEquality
open NumberedWindowRawWitnessBits NumberedWindowRawWitnessLaws NumberedWindowRawWitnessRootBuild

theorem lam {S K σ Q R} (h : TermCert S K Q R) :
    TermCert S K (.lam σ Q) (.lam σ R) := by
  obtain ⟨w,hw⟩ := h
  exact ⟨.lam w,by simp [rawBit,hw]⟩

theorem ordinaryBase {S K f qs rs} (h : ArgsCert S K qs rs) :
    TermCert S K (.ordinary f qs) (.ordinary f rs) := by
  obtain ⟨i,w,hw⟩ := h
  refine ⟨.ordinaryBase i w,?_⟩
  change (decide (f = f) && argsAtBit (rawBit S K w) i qs rs) = true
  simp [hw]

theorem numberedBase {S K f τ k bs bt es} (h : ArgsCert S K bs bt) :
    TermCert S K (.numbered f τ k bs es) (.numbered f τ k bt es) := by
  obtain ⟨i,w,hw⟩ := h
  refine ⟨.numberedBase i w,?_⟩
  change (decide (f = f) && decide (τ = τ) && decide (k = k) && argsEq es es &&
    argsAtBit (rawBit S K w) i bs bt) = true
  simp [hw,argsRefl]

theorem numberedExtra {S K f τ k bs es et} (h : ArgsCert S K es et) :
    TermCert S K (.numbered f τ k bs es) (.numbered f τ k bs et) := by
  obtain ⟨i,w,hw⟩ := h
  refine ⟨.numberedExtra i w,?_⟩
  change (decide (f = f) && decide (τ = τ) && decide (k = k) && argsEq bs bs &&
    argsAtBit (rawBit S K w) i es et) = true
  simp [hw,argsRefl]

theorem auxFunction {S K σ τ Q R A} (h : TermCert S K Q R) :
    TermCert S K (.auxApp σ τ Q A) (.auxApp σ τ R A) := by
  obtain ⟨w,hw⟩ := h
  exact ⟨.auxFunction w,by simp [rawBit,hw,termRefl]⟩

theorem first {S K Q R qs} (h : TermCert S K Q R) :
    ArgsCert S K (.cons Q qs) (.cons R qs) := by
  obtain ⟨w,hw⟩ := h
  exact ⟨0,w,by simp [argsAtBit,hw,argsRefl]⟩

theorem later {S K Q qs rs} (h : ArgsCert S K qs rs) :
    ArgsCert S K (.cons Q qs) (.cons Q rs) := by
  obtain ⟨i,w,hw⟩ := h
  exact ⟨i+1,w,by simp [argsAtBit,hw,termRefl]⟩

end LogicLineages.PersistentMarking.NumberedWindowRawWitnessContextBuild
