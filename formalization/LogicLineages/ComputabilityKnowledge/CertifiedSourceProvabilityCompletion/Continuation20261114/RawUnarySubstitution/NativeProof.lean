module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution.NativeProof
open GorbowSyntax GorbowPRProgram List.Vector SixSol20261113 HistoryRuleSuffix
open SixSol20261113.HistoryRuleSuffix.NativeProof

theorem nativeSubstitution : Targets.NativeSubstitution := by
 intro t u
 have hc (a b : Nat) : evaluate HistoryCodec.cons (a ::ᵥ b ::ᵥ nil) = (Nat.pair a b).succ :=
  HistoryCodec.NativeProof.nativeConsAllVectors _
 induction t with
 | var i =>
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl
 | zero => rfl
 | succ t ih =>
  simp only [program,twoEval,constantEval,ih,hc,GorbowSubstitution.substitute,GorbowTermPrefixCode.encode]
  rfl
 | add t v ht hv =>
  simp only [program,twoEval,constantEval,ht,hv,appendList,hc,GorbowSubstitution.substitute,GorbowTermPrefixCode.encode]
  rfl
 | mul t v ht hv =>
  simp only [program,twoEval,constantEval,ht,hv,appendList,hc,GorbowSubstitution.substitute,GorbowTermPrefixCode.encode]
  rfl
 | universalFunction t ih =>
  simp only [program,twoEval,constantEval,ih,hc,GorbowSubstitution.substitute,GorbowTermPrefixCode.encode]
  rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution.NativeProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnarySubstitution.NativeProof.nativeSubstitution
