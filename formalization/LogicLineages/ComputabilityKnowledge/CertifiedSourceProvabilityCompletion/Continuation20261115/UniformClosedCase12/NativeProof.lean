module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.NativeCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.NativeProof
open GorbowPRProgram SixSol20261113 List.Vector HistoryRuleSuffix.NativeProof NativeAtomsProof NativeCasesProof
open UniformClosedCase13.NativeAtomsProof (noneCode someCode successorEval)
theorem originalLists (args : List (List Nat)) :
 evaluate caseCode (Encodable.encode args ::ᵥ nil) = Encodable.encode (GorbowLogicalAxiomCode.case12 0 args) := by
 rw [caseCode,chooseEval,lengthTest]
 by_cases hl : args.length = 3
 · simp only [hl,ite_true,Nat.one_ne_zero,ite_false]
   obtain ⟨f,t,u,rfl⟩ := List.length_eq_three.mp hl
   rw [originalTriple,chooseEval,leftAt]
   cases hi : GorbowInstanceCode.instanceCode 0 f t with
   | none =>
    simp only [noneCode,ite_true,constantEval,Option.bind_none]
   | some left =>
    simp only [someCode,Nat.succ_ne_zero,ite_false,Option.bind_some]
    rw [chooseEval,rightAt]
    cases hj : GorbowInstanceCode.instanceCode 0 f u with
    | none =>
     simp only [noneCode,ite_true,constantEval,Option.bind_none]
    | some right =>
     simp only [someCode,Nat.succ_ne_zero,ite_false,Option.bind_some]
     rw [oneEval,implicationAt f t u left right hi hj,successorEval]
     exact (someCode _).symm
 · rw [originalWrongLength args hl]
   simp only [hl,ite_false,ite_true,constantEval,noneCode]
theorem exactOriginalCase12 : Targets.ExactOriginalCase12 := by
 intro code
 obtain ⟨args,he⟩ := HistoryKernel.CodecTotalProof.listTotal
  (HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal) code
 rw [← he]
 simp only [decodedArguments,Encodable.encodek,Option.getD_some]
 exact originalLists args
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.NativeProof
