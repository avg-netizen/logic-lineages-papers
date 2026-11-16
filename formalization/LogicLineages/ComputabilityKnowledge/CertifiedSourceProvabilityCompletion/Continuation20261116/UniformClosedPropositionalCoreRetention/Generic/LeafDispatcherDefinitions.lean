module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Generic.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalDispatcherRetention.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Generic.LeafDispatcher
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Actual old dispatcher, with arbitrary original validity/arithmetic/source leaves. -/
abbrev original (valid old arithmetic : Program 1) (x : Program 3) : Program 4 :=
 HistoryDispatcher.lineDispatcher valid old arithmetic x
/-- Only the actual logical leaf changes, through two nested conservative selectors. -/
abbrev extended (testK testS valid old arithmetic : Program 1) (x : Program 3) : Program 4 :=
 HistoryDispatcher.lineDispatcher valid (extend testK testS old) arithmetic x
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.Generic.LeafDispatcher
