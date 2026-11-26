module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Targets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Generic
open GorbowPRProgram SixSol20261113
/-- Private reusable selector extension. No hypothesis on recognizer behavior. -/
abbrev extend (testK testS old : Program 1) : Program 1 :=
 HistoryRuleSuffix.choose testS
  (HistoryRuleSuffix.choose testK old (HistoryRuleSuffix.constant 1 1))
  (HistoryRuleSuffix.constant 1 1)
abbrev original (valid logical arithmetic : Program 1) (x : Program 3) : Program 5 :=
 LiteralKernelSource.coreChecker valid logical arithmetic x LiteralCheckerAuxiliaries.bound
  LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer
abbrev extended (testK testS valid logical arithmetic : Program 1) (x : Program 3) : Program 5 :=
 original valid (extend testK testS logical) arithmetic x
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Generic
