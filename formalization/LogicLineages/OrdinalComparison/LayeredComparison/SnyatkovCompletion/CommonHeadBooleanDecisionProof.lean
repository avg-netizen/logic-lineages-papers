module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBooleanSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBooleanCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceDecisionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBooleanProof
open CommonLayerSyntax CommonHeadBoolean

theorem actualBlockDecisions : CommonHeadBooleanTargets.ActualBlockDecisions := by
  intro Γ hg xs values p b
  have h := BaseBooleanSourceProof.actualBlockDecisions xs values (translate (headCodes Γ) p) b
  have he := (exactPrefixTranslation Γ hg xs p (PlainParameterDecision.valuation values)).1
  have ha := (exactPrefixTranslation Γ hg xs p (PlainParameterDecision.valuation values)).2
  rw [he, ha] at h
  rw [Code.decideExists, Code.decideForall, literalCompiler]
  exact h

theorem actualClosureDecisions : CommonHeadBooleanTargets.ActualClosureDecisions := by
  intro Γ hg p b
  have h := BaseBooleanSourceProof.actualClosureDecisions (translate (headCodes Γ) p) b
  rw [exists_congr (fun ν => exactTranslation Γ hg p ν),
    forall_congr' (fun ν => exactTranslation Γ hg p ν)] at h
  rw [Code.decideClosureExists, Code.decideClosureForall, literalCompiler]
  exact h

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBooleanProof
