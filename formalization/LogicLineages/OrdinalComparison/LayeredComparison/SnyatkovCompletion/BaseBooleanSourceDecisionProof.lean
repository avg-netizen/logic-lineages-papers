module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceProof
open BaseBooleanSource

theorem actualBlockDecisions : BaseBooleanSourceTargets.ActualBlockDecisions := by
  intro xs values p b
  have hp := (exactSourceData p).1
  have h := SourceParameterDecisionProof.actualSourceDecisions xs values (translate p) hp b
  have he := (exactPrefixTranslation xs p (PlainParameterDecision.valuation values)).1
  have ha := (exactPrefixTranslation xs p (PlainParameterDecision.valuation values)).2
  rw [Code.decideExists, Code.decideForall, literalCompiler,
    SourceParameterDecisionProof.decideExists_calibration, SourceParameterDecisionProof.decideForall_calibration]
  rw [he, ha] at h
  exact h

theorem actualClosureDecisions : BaseBooleanSourceTargets.ActualClosureDecisions := by
  intro p b
  have h := SourceBooleanProgramsProof.actualEncodedDecisions (translate p) (exactSourceData p).1 b
  have he : (∃ ν : Nat → Nat, (translate p).eval ν) ↔ ∃ ν : Nat → Nat, p.eval ν :=
    exists_congr (fun ν => exactTranslation p ν)
  have ha : (∀ ν : Nat → Nat, (translate p).eval ν) ↔ ∀ ν : Nat → Nat, p.eval ν :=
    forall_congr' (fun ν => exactTranslation p ν)
  rw [Code.decideClosureExists, Code.decideClosureForall, literalCompiler]
  rw [he, ha] at h
  exact h

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceProof
