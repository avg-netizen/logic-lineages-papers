module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositional.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention
open GorbowPRProgram SixSol20261113
/-- Actual previous checker; the logical leaf may already carry all Rule12 and
Rule13 capabilities. No restriction on malformed numeric certificates. -/
abbrev original (valid logical arithmetic : Program 1) (x : Program 3) : Program 5 :=
 LiteralKernelSource.coreChecker valid logical arithmetic x
  LiteralCheckerAuxiliaries.bound LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer
/-- Only the logical leaf is changed, by precisely the checked K/S extension. -/
abbrev extended (valid logical arithmetic : Program 1) (x : Program 3) : Program 5 :=
 original valid (UniformClosedPropositional.logicalLeaf logical) arithmetic x
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention
