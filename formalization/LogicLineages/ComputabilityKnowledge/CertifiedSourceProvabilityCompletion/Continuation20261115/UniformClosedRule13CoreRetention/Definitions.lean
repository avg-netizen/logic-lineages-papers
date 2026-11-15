module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCoreRetention.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention
open GorbowPRProgram SixSol20261113
/-- Original literal CORE, code-bound iteration and unchanged initial/final states. -/
abbrev original (valid logical arithmetic : Program 1) (x : Program 3) : Program 5 :=
 LiteralKernelSource.coreChecker valid logical arithmetic x LiteralCheckerAuxiliaries.bound
  LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer
/-- Sole change: runtime uniform rule13 recognizer with literal old fallback. -/
abbrev extended (valid logical arithmetic : Program 1) (x : Program 3) : Program 5 :=
 original valid (UniformClosedRule13.logicalLeaf logical) arithmetic x
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13CoreRetention
