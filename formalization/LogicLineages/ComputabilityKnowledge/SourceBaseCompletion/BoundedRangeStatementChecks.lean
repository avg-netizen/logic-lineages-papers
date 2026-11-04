module

public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BoundedRangeTargets
public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BoundedRangeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BoundedRange.StatementChecks

theorem compilerGuard : Targets.CompilerGuard := Proof.compilerGuard
theorem guardSemantics : Targets.GuardSemantics := Proof.guardSemantics
theorem rangeElimination : Targets.RangeElimination := Proof.rangeElimination
theorem boundedGeneralization : Targets.BoundedGeneralization := Proof.boundedGeneralization
theorem boundedRange : Targets.Target := Proof.fullTarget

#print axioms compilerGuard
#print axioms guardSemantics
#print axioms rangeElimination
#print axioms boundedGeneralization
#print axioms boundedRange

end LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BoundedRange.StatementChecks
