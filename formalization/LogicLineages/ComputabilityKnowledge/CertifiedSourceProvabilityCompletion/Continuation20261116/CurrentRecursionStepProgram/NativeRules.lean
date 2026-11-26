module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeOperations
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeRules
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof
open HistoryRuleSuffix.NativeProof PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication
open NativeOperations

theorem unaryEval {arity : Nat} (openCode t u ft fu : Program arity) (v : List.Vector Nat arity)
 (f : Term 1) (a b : Term 0)
 (ho : evaluate openCode v = Encodable.encode (GorbowTermPrefixCode.encode f))
 (ht : evaluate t v = Encodable.encode (GorbowTermPrefixCode.encode a))
 (hu : evaluate u v = Encodable.encode (GorbowTermPrefixCode.encode b))
 (hft : evaluate ft v = Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.instantiateTerm f a)))
 (hfu : evaluate fu v = Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.instantiateTerm f b))) :
 evaluate (unaryRule openCode t u ft fu) v = unaryRuleNumber f a b := by
 let fa := GorbowClosedEquality.instantiateTerm f a
 let fb := GorbowClosedEquality.instantiateTerm f b
 have hP := equalEval t u v a b ht hu
 have hQ := equalEval ft ft v fa fa hft hft
 have hR := equalEval ft fu v fa fb hft hfu
 have hmatrix : evaluate (FixedFormulaSubstitution.binary 0 ft openCode) v =
  Encodable.encode (GorbowFormulaPrefixCode.encode (.equal (GorbowClosedEquality.liftClosedTerm 1 fa) f)) := by
  simpa only [GorbowFormulaPrefixCode.encode,PrescribedRuntimeEquality.EncodingProof.liftEncode] using
   binaryEval 0 ft openCode v (GorbowTermPrefixCode.encode fa) (GorbowTermPrefixCode.encode f) hft ho
 unfold unaryRule
 rw [mpUnderEval _ _ _ _ _ v _ _ _ hP hQ hR,
  replacementEval _ _ _ v _ _ _ hmatrix ht hu,liftEval _ _ _ v _ _ hQ hP,reflexivityEval _ v fa hft]
 rfl

theorem transitivityEval {arity : Nat} (P left middle right hleft hright : Program arity) (v : List.Vector Nat arity)
 (phi : Formula 0) (t u w : Term 0)
 (hP : evaluate P v = Encodable.encode (GorbowFormulaPrefixCode.encode phi))
 (ht : evaluate left v = Encodable.encode (GorbowTermPrefixCode.encode t))
 (hu : evaluate middle v = Encodable.encode (GorbowTermPrefixCode.encode u))
 (hw : evaluate right v = Encodable.encode (GorbowTermPrefixCode.encode w)) :
 evaluate (transitivityUnder P left middle right hleft hright) v =
 transitivityUnderNumber phi t u w (evaluate hleft v) (evaluate hright v) := by
 have hTU := equalEval left middle v t u ht hu
 have hUV := equalEval middle right v u w hu hw
 have hTV := equalEval left right v t w ht hw
 have hmatrix := headQuoteEval (.equal (.var 1) (.var 0) : Formula 2) (fun _ => left) v (fun _ : Fin 1 => t) (fun _ => ht)
 rw [CurrentRecursionBaseProgram.TransitivityNativeProof.matrix] at hmatrix
 unfold transitivityUnder
 rw [mpUnderEval _ _ _ _ _ v _ _ _ hP hTU hTV]
 rw [mpUnderEval _ _ _ _ _ v _ _ _ hP hUV (impEval _ _ v _ _ hTU hTV)]
 rw [liftEval _ _ _ v _ _ (impEval _ _ v _ _ hUV (impEval _ _ v _ _ hTU hTV)) hP]
 rw [replacementEval _ _ _ v _ _ _ hmatrix hu hw]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeRules
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeRules
