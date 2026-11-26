module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeRules
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeQuotes
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeAssembly
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof
open HistoryRuleSuffix HistoryRuleSuffix.NativeProof PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication
open NativeOperations NativeRules NativeQuotes

theorem assembled {arity : Nat} (v : List.Vector Nat arity)
 (prior priorNum next left right output openCode seed child : Program arity)
 (pc pn nc l r o : Term 0) (f : Term 1)
 (hpc : evaluate prior v = Encodable.encode (GorbowTermPrefixCode.encode pc))
 (hpn : evaluate priorNum v = Encodable.encode (GorbowTermPrefixCode.encode pn))
 (hnc : evaluate next v = Encodable.encode (GorbowTermPrefixCode.encode nc))
 (hl : evaluate left v = Encodable.encode (GorbowTermPrefixCode.encode l))
 (hr : evaluate right v = Encodable.encode (GorbowTermPrefixCode.encode r))
 (ho : evaluate output v = Encodable.encode (GorbowTermPrefixCode.encode o))
 (hf : evaluate openCode v = Encodable.encode (GorbowTermPrefixCode.encode f))
 (hlf : evaluate left v = Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.instantiateTerm f pc)))
 (hrf : evaluate right v = Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.instantiateTerm f pn))) :
 let P := FixedFormulaSubstitution.binary 0 prior priorNum
 evaluate (transitivityUnder P next right output
  (transitivityUnder P next left right
   (liftProgram (FixedFormulaSubstitution.binary 0 next left) P seed)
   (unaryRule openCode prior priorNum left right))
  (liftProgram (FixedFormulaSubstitution.binary 0 right output) P child)) v =
 transitivityUnderNumber (.equal pc pn) nc r o
  (transitivityUnderNumber (.equal pc pn) nc l r
   (liftNumber (.equal nc l) (.equal pc pn) (evaluate seed v)) (unaryRuleNumber f pc pn))
  (liftNumber (.equal r o) (.equal pc pn) (evaluate child v)) := by
 dsimp only
 have hP := equalEval prior priorNum v pc pn hpc hpn
 have hroot := equalEval next left v nc l hnc hl
 have hchild := equalEval right output v r o hr ho
 rw [NativeRules.transitivityEval _ _ _ _ _ _ v (.equal pc pn) nc r o hP hnc hr ho]
 rw [NativeRules.transitivityEval _ _ _ _ _ _ v (.equal pc pn) nc l r hP hnc hl hr]
 rw [liftEval _ _ _ v _ _ hroot hP,unaryEval _ _ _ _ _ v f pc pn hf hpc hpn hlf hrf,
  liftEval _ _ _ v _ _ hchild hP]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeAssembly
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeAssembly
