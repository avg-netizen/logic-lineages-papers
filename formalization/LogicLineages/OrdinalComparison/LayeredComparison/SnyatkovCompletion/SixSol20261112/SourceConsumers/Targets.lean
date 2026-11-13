module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceConsumers.Definitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariablesTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedFirstOrderTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceConsumersTargets
open SourceConsumers

/-- Every certified CLOSED original common-head formula, arbitrary Boolean and
quantifier alternation, each atom's own actual head list and literal raw names.
Both Nat and positive binders retain their displayed domains. -/
def ActualCommonDecision : Prop :=
  Computable commonAnswer ∧
  (∀ p : CommonHeadFirstOrder.Formula,
    commonAnswer p.encode = SourceDecision.answer (CommonHeadFirstOrder.translate p).encode) ∧
  ∀ p : CommonHeadFirstOrder.Formula, p.certified → p.variables = [] → ∀ ν : Nat → Nat,
    commonAnswer p.encode = true ↔ p.eval ν

/-- Every certified CLOSED original balanced formula. The source's raw variables
and binders range positively; no positivity assumption is imposed on an old
shadowed name or outside coordinate. Whole pair certificates are never split. -/
def ActualBalancedDecision : Prop :=
  Computable balancedAnswer ∧
  (∀ p : BalancedFirstOrder.Formula,
    balancedAnswer p.encode = SourceDecision.answer (BalancedFirstOrder.translate p).encode) ∧
  ∀ p : BalancedFirstOrder.Formula, p.certified → p.variables = [] → ∀ ν : Nat → Nat,
    balancedAnswer p.encode = true ↔ p.eval ν

/-- ENTIRE source08 thm:common: actual pointwise BASE formula/code, literal exact
original raw free-variable membership, actual numeric effectivity, full Boolean/
quantified translation with exact free names/domains, and a proved closed solver. -/
def FullCommonHeadLayers : Prop :=
  CommonHeadExactVariablesTargets.ActualSourceClause ∧
  CommonHeadExactVariablesTargets.LiteralCodeCalibration ∧
  CommonHeadExactVariablesTargets.ActualOutputProgram ∧
  CommonHeadFirstOrderTargets.ActualSourceTranslation ∧
  CommonHeadFirstOrderTargets.ExactFreeVariables ∧
  CommonHeadFirstOrderTargets.ExactUniversalDomains ∧
  ActualCommonDecision

/-- ENTIRE source08 thm:balanced, retaining one original whole pair certificate,
shared basis (including dependent/repeated entries), remainder support and the
source positive domain. The numeric solver is proved here, never assumed. -/
def FullBalancedComparison : Prop :=
  BalancedExactVariables.Targets.TruthAndExactVariables ∧
  BalancedExactVariables.Targets.ActualSignSemantics ∧
  BalancedExactVariables.Targets.ExactTypedCodeCalibration ∧
  BalancedExactVariables.Targets.AllCodeComputation ∧
  BalancedFirstOrderTargets.ActualSourceTranslation ∧
  BalancedFirstOrderTargets.ExactFreeVariables ∧
  BalancedFirstOrderTargets.ExactUniversalDomain ∧
  ActualBalancedDecision

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceConsumersTargets
