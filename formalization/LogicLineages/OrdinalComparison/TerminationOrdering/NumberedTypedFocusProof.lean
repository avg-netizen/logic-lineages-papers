module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedFocusSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedFocusProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedStepContexts NumberedTypedFocus

theorem termFocusReconstruction : NumberedTypedFocusTargets.ActualTermFocusReconstruction := NumberedTypedFocusSupportProof.termFocusReconstruction
theorem argumentFocusReconstruction : NumberedTypedFocusTargets.ActualArgumentFocusReconstruction := NumberedTypedFocusSupportProof.argumentFocusReconstruction

theorem termFocusCoverage : NumberedTypedFocusTargets.ActualTermFocusCoverage := by
  intro n arity holeGamma holeType Gamma tau context q
  induction context using TermContext.rec
    (motive_2 := fun Gamma types context => ∃ path index,focusArguments path index (plugArguments context q)=some (⟨holeGamma,holeType,context,q⟩ : ArgumentFocus n arity Gamma types))
  case hole => exact ⟨[],by simp [plug,focus]⟩
  case lam body ih =>
    obtain ⟨path,h⟩ := ih
    exact ⟨.lam::path,by simp [plug,focus,h]⟩
  case appFunction fn arg ih =>
    obtain ⟨path,h⟩ := ih
    exact ⟨.appFunction::path,by simp [plug,focus,h]⟩
  case ordinary head base ih =>
    obtain ⟨path,index,h⟩ := ih
    simp only [focusArguments] at h
    exact ⟨.ordinaryBase index::path,by simp [plug,focus,h]⟩
  case numberedBase label head tau base types extras ih =>
    obtain ⟨path,index,h⟩ := ih
    simp only [focusArguments] at h
    exact ⟨.numberedBase index::path,by simp [plug,focus,h]⟩
  case numberedExtras label head tau base types extras ih =>
    obtain ⟨path,index,h⟩ := ih
    simp only [focusArguments] at h
    exact ⟨.numberedExtras index::path,by simp [plug,focus,h]⟩
  case head first rest ih =>
    obtain ⟨path,h⟩ := ih
    exact ⟨path,0,by simp [plugArguments,focusArguments,argumentFocusWith,h]⟩
  case tail first rest ih =>
    obtain ⟨path,index,h⟩ := ih
    simp only [focusArguments] at h
    exact ⟨path,index+1,by simp [plugArguments,focusArguments,argumentFocusWith,h]⟩

theorem argumentFocusCoverage : NumberedTypedFocusTargets.ActualArgumentFocusCoverage := by
  intro n arity holeGamma holeType Gamma types context q
  induction context using ArgumentContext.rec
    (motive_1 := fun Gamma tau context => ∃ path,focus path (plug context q)=some (⟨holeGamma,holeType,context,q⟩ : TermFocus n arity Gamma tau))
  case hole => exact ⟨[],by simp [plug,focus]⟩
  case lam body ih =>
    obtain ⟨path,h⟩ := ih
    exact ⟨.lam::path,by simp [plug,focus,h]⟩
  case appFunction fn arg ih =>
    obtain ⟨path,h⟩ := ih
    exact ⟨.appFunction::path,by simp [plug,focus,h]⟩
  case ordinary head base ih =>
    obtain ⟨path,index,h⟩ := ih
    simp only [focusArguments] at h
    exact ⟨.ordinaryBase index::path,by simp [plug,focus,h]⟩
  case numberedBase label head tau base types extras ih =>
    obtain ⟨path,index,h⟩ := ih
    simp only [focusArguments] at h
    exact ⟨.numberedBase index::path,by simp [plug,focus,h]⟩
  case numberedExtras label head tau base types extras ih =>
    obtain ⟨path,index,h⟩ := ih
    simp only [focusArguments] at h
    exact ⟨.numberedExtras index::path,by simp [plug,focus,h]⟩
  case head first rest ih =>
    obtain ⟨path,h⟩ := ih
    exact ⟨path,0,by simp [plugArguments,focusArguments,argumentFocusWith,h]⟩
  case tail first rest ih =>
    obtain ⟨path,index,h⟩ := ih
    simp only [focusArguments] at h
    exact ⟨path,index+1,by simp [plugArguments,focusArguments,argumentFocusWith,h]⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedFocusProof
