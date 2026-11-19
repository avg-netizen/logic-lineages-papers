module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionWorkingDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.CertifiedCommonTargets
open OrdinalComparison LayeredComparison.SnyatkovCompletion SixSol20261112

/-- All three pointwise comparisons at every genuine fixed head list, computed
as base formulas with exact original raw free names. The truth clause actually
holds for every Nat valuation and hence for every positive valuation. -/
def ExactPointwise : Prop :=
  CommonHeadExactVariablesTargets.ActualSourceClause ∧
  CommonHeadExactVariablesTargets.LiteralCodeCalibration ∧
  CommonHeadExactVariablesTargets.ActualOutputProgram

/-- Each atom keeps its own finite certificate, and the original quantifiers
retain raw name scope, shadowing and the exact Nat/positive domains. -/
def ExactTranslation : Prop :=
  CommonHeadFirstOrderTargets.ActualSourceTranslation ∧
  CommonHeadFirstOrderTargets.ExactFreeVariables ∧
  CommonHeadFirstOrderTargets.LiteralCodeCalibration ∧
  CommonHeadFirstOrderTargets.ActualNumericProgram ∧
  CommonHeadFirstOrderTargets.ExactUniversalDomains

/-- The actual total computed decision, with no supplied solver or limited
binder prefix. Only genuine certification and sentence closure delimit the
original semantic input, not computability on numeric codes. -/
def ActualClosedAnswer : Prop :=
  Computable (fun code : Nat => SourceDecision.answer (CommonHeadFirstOrder.Code.translate code)) ∧
  (∀ p : CommonHeadFirstOrder.Formula,
    SourceDecision.answer (CommonHeadFirstOrder.Code.translate p.encode) =
      SourceDecision.answer (CommonHeadFirstOrder.translate p).encode) ∧
  ∀ p : CommonHeadFirstOrder.Formula, p.certified → p.variables = [] → ∀ ν : Nat → Nat,
    SourceDecision.answer (CommonHeadFirstOrder.Code.translate p.encode) = true ↔ p.eval ν

/-- Paper18 m:thm:common, certified-fragments.tex 45–51, including both the
unrestricted pointwise source translation and the closed decision conclusion. -/
def FullCommonHeadLayers : Prop := ExactPointwise ∧ ExactTranslation ∧ ActualClosedAnswer

end LogicLineages.StandardControlCurrent.CertifiedCommonTargets
