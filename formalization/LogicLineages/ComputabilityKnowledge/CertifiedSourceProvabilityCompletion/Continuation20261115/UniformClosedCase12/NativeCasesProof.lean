module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.NativeAtomsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.NativeCasesProof
open GorbowPRProgram SixSol20261113 HistoryRuleSuffix List.Vector HistoryRuleSuffix.NativeProof
/-- Small literal length test only; the instance AST is not unfolded here. -/
theorem lengthTest (args : List (List Nat)) :
 evaluate (applyTwo equalCode HistoryLengthOffset.lengthProgram (constant 1 3)) (Encodable.encode args ::ᵥ nil) =
 if args.length = 3 then 1 else 0 := by
 rw [twoEval,HistoryLengthOffset.NativeProof.lengthList,constantEval,equalEval]
/-- Isolate original Option sequencing from the installed evaluator. -/
theorem originalTriple (f t u : List Nat) :
 GorbowLogicalAxiomCode.case12 0 [f,t,u] =
 (GorbowInstanceCode.instanceCode 0 f t).bind (fun left =>
  (GorbowInstanceCode.instanceCode 0 f u).bind (fun right =>
   some (GorbowCodeConstructors.binary 7 (GorbowCodeConstructors.binary 0 t u)
    (GorbowCodeConstructors.binary 7 left right)))) := rfl
theorem originalWrongLength (args : List (List Nat)) (h : args.length ≠ 3) :
 GorbowLogicalAxiomCode.case12 0 args = none := by
 simp only [GorbowLogicalAxiomCode.case12,h,ite_false]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.NativeCasesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.NativeCasesProof
