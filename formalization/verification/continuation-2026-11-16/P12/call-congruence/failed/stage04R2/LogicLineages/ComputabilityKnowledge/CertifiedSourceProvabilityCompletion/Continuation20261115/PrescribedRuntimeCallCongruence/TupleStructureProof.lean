module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TupleStructureProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem vectorZero {α : Type} (v : List.Vector α 0) : v = nil := by
 apply List.Vector.ext
 intro i
 exact Fin.elim0 i
theorem zero {ctx : Nat} (J : Tags) (v : List.Vector (Term ctx) 0) : tupleValue J v.toList = zeroValue := by
 rw [vectorZero v]
 rfl
theorem succ {ctx n : Nat} (J : Tags) (v : List.Vector (Term ctx) (n+1)) :
 tupleValue J v.toList = FixedFormulaSubstitution.unaryValue J.ctag 2
  (pairValue J v.head (tupleValue J v.tail.toList)) := by
 rw [← List.Vector.cons_head_tail v]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TupleStructureProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.TupleStructureProof
