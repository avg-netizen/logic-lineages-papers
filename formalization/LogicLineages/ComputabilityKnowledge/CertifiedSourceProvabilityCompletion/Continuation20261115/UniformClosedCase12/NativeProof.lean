module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.NativeAtomsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.NativeProof
open GorbowPRProgram SixSol20261113 List.Vector HistoryRuleSuffix.NativeProof NativeAtomsProof
open UniformClosedCase13.NativeAtomsProof (noneCode someCode successorEval)
theorem originalLists (args : List (List Nat)) :
 evaluate caseCode (Encodable.encode args ::ᵥ nil) = Encodable.encode (GorbowLogicalAxiomCode.case12 0 args) := by
 simp only [caseCode,chooseEval,twoEval,constantEval,HistoryLengthOffset.NativeProof.lengthList,equalEval]
 by_cases hl : args.length = 3
 · simp only [hl,ite_true,Nat.one_ne_zero,ite_false]
   obtain ⟨f,t,u,rfl⟩ := List.length_eq_three.mp hl
   rw [leftAt]
   cases hi : GorbowInstanceCode.instanceCode 0 f t with
   | none =>
    simp [noneCode,GorbowLogicalAxiomCode.case12,GorbowLogicalAxiomCode.arg,hi]
   | some left =>
    rw [someCode]
    simp only [Nat.succ_ne_zero,ite_false]
    rw [rightAt]
    cases hj : GorbowInstanceCode.instanceCode 0 f u with
    | none =>
     simp [noneCode,GorbowLogicalAxiomCode.case12,GorbowLogicalAxiomCode.arg,hi,hj]
    | some right =>
     rw [someCode]
     simp only [Nat.succ_ne_zero,ite_false,oneEval,successorEval]
     rw [implicationAt f t u left right hi hj]
     simp [GorbowLogicalAxiomCode.case12,GorbowLogicalAxiomCode.arg,hi,hj,someCode]
 · simp [hl,GorbowLogicalAxiomCode.case12,noneCode]
theorem exactOriginalCase12 : Targets.ExactOriginalCase12 := by
 intro code
 obtain ⟨args,he⟩ := HistoryKernel.CodecTotalProof.listTotal
  (HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal) code
 rw [← he]
 simp only [decodedArguments,Encodable.encodek,Option.getD_some]
 exact originalLists args
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.NativeProof
