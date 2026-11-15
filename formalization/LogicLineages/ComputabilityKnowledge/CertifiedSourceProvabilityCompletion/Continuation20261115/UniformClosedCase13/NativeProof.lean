module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.NativeAtomsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.NativeProof
open GorbowPRProgram SixSol20261113 List.Vector HistoryRuleSuffix.NativeProof NativeAtomsProof
/-- Whole original annotation lists: wrong lengths reject before any successful
instance calibration is needed; valid lengths retain original Option cases. -/
theorem exactOriginalCase13 : Targets.ExactOriginalCase13 := by
 intro args
 simp only [caseCode,chooseEval,twoEval,constantEval,HistoryLengthOffset.NativeProof.lengthList,equalEval]
 by_cases hl : args.length = 2
 · simp only [hl,ite_true,Nat.one_ne_zero,ite_false]
   obtain ⟨f,t,rfl⟩ := List.length_eq_two.mp hl
   rw [instanceAt]
   cases hi : GorbowInstanceCode.instanceCode 0 f t with
   | none =>
    simp [noneCode,GorbowLogicalAxiomCode.case13,GorbowLogicalAxiomCode.arg,hi]
   | some result =>
    rw [someCode]
    simp only [Nat.succ_ne_zero,ite_false,oneEval,successorEval]
    rw [implicationAt f t result hi]
    simp [GorbowLogicalAxiomCode.case13,GorbowLogicalAxiomCode.arg,hi,someCode]
 · simp [hl,GorbowLogicalAxiomCode.case13,noneCode]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.NativeProof
