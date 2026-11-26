module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationRetention.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCoreRetention.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCoreRetention
open GorbowSyntax GorbowPRProgram SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Original CORE with original encoded-certificate bound, initializer and finalizer. -/
abbrev original (valid logical arithmetic : Program 1) (x : Program 3) : Program 5 :=
 LiteralKernelSource.coreChecker valid logical arithmetic x LiteralCheckerAuxiliaries.bound
  LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer
/-- Only the old logical leaf is extended by the literal fixed tag13 recognizer.
No runtime, input, bound, initialization, or finalization convention changes. -/
abbrev extended (f : Formula 1) (valid logical arithmetic : Program 1) (x : Program 3) : Program 5 :=
 original valid (FullFormulaInstantiation.logicalLeaf f logical) arithmetic x
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCoreRetention
