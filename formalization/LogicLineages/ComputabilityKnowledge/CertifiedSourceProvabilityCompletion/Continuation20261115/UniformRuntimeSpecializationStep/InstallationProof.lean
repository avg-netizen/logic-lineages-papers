module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeSpecializationStep.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeSpecializationStep.InstallationProof
open GorbowPRProgram GorbowPRRegistry SixSol20261113
theorem dropNode {arity : Nat} (p : Program arity) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule13Certificate.Installation p old arithmetic x) :
 (nodes p)[HistoryLookup.LookupProof.dropTag I.qtag]? = some ⟨2,HistoryLookup.drop⟩ := by
 exact SixSol20261112.Fuel.Equations.argumentChild p I.qtag HistoryLookup.reference
  (fun _ : Fin 1 => HistoryLookup.drop) I.h_qtag 0
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeSpecializationStep.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeSpecializationStep.InstallationProof
