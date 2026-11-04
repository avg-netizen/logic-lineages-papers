module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.TargetChecks
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.AssemblyProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.StatementChecks

theorem source_process_bridge : Targets.SourceProcessBridge := Proof.sourceProcessBridge
theorem signed_domain_contract : Targets.SignedDomainContract := Proof.signedDomainContract
theorem corrected_kernel_recursion : Targets.CorrectedKernelRecursion := Proof.correctedKernelRecursion
theorem corrected_counter_source : Targets.CorrectedCounterSource := Proof.correctedCounterSource
theorem corrected_kernel_residues : Targets.CorrectedKernelResidues := Proof.correctedKernelResidues

end LogicLineages.OrdinalComparison.KernelSourceCompletion.StatementChecks

#audit_namespace LogicLineages.OrdinalComparison.KernelSourceCompletion
