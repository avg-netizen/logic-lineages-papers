module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.Targets
public import LogicLineages.ComputabilityKnowledge.GorbowPRRegistryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.OccurrenceProof
open GorbowPRProgram GorbowPRRegistry HistoryLengthOffset HistoryRuleSuffix

theorem lineOccurs : Occurs ⟨3,lineProgram⟩ constructor := by
 apply Occurs.compositionArgument _ _ (1 : Fin 2)
 apply Occurs.compositionArgument _ _ (0 : Fin 2)
 exact Occurs.compositionFunction _ _ (.here _ rfl)

theorem lengthOccurs : Occurs ⟨1,lengthProgram⟩ constructor := by
 apply Occurs.compositionArgument _ _ (1 : Fin 2)
 apply Occurs.compositionArgument _ _ (0 : Fin 2)
 apply Occurs.compositionArgument _ _ (2 : Fin 3)
 exact Occurs.compositionFunction _ _ (.here _ rfl)

theorem actualChildren : Targets.ActualChildren := by
 obtain ⟨lt,_,hl⟩ := (GorbowPRRegistry.Proof.taggedCoverage 4 constructor ⟨1,lengthProgram⟩).mp lengthOccurs
 obtain ⟨rt,_,hr⟩ := (GorbowPRRegistry.Proof.taggedCoverage 4 constructor ⟨3,lineProgram⟩).mp lineOccurs
 exact ⟨lt,rt,hl,hr⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.OccurrenceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.OccurrenceProof
