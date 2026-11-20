import LogicLineages.PersistentMarking.NumberedWindowRootDispatchAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowRawContextTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticMarkRootTargets

namespace LogicLineages.PersistentMarking.NumberedWindowRootDispatchTargets
open NumberedWindowRootDispatchAlgorithm NumberedWindowArithmeticTyCode
open NumberedWindowArithmeticRawRootCode NumberedWindowArithmeticMarkRootTargets

structure RuleCalibration (S : Spine.Signature) (K : List Ty) (rules : Rules) : Prop where
  mark : ∀ k, rules.mark k = rootOn S K (.mark k)
  lower : rules.lower = rootOn S K .lower
  select : ∀ extra i domains,
    rules.select extra i (domains.map encodeTy) = rootOn S K (.select extra i domains)
  copy : rules.copy = rootOn S K .copy
  stat : ∀ p, rules.stat (encodeReplacement p) = rootOn S K (.stat p)
  fabs : rules.fabs = rootOn S K .fabs
  beta : rules.beta = rootOn S K .beta
  bottom : rules.bottom = rootOn S K .bottom

def ExactRootDispatch : Prop := ∀ S K rules, RuleCalibration S K rules →
  NumberedWindowRawContextTargets.RootCalibration S K (check rules)

end LogicLineages.PersistentMarking.NumberedWindowRootDispatchTargets
