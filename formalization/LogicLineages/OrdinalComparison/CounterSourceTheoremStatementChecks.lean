module
public import LogicLineages.OrdinalComparison.CounterSourceTheoremTargets
public import LogicLineages.OrdinalComparison.CounterSourceTheoremProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterSourceTheorem.StatementChecks
theorem actual_kernel_startup : Targets.ActualKernelStartup := Proof.actualKernelStartup
theorem uniform_tail_programs : Targets.UniformTailPrograms := Proof.uniformTailPrograms
theorem whole_counter_lemma : Targets.WholeCounterLemma := Proof.wholeCounterLemma
end LogicLineages.OrdinalComparison.CounterSourceTheorem.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.CounterSourceTheorem
