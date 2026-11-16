module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeUnary
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof
open HistoryRuleSuffix.NativeProof

theorem quoteTerm {arity n depth rawCount : Nat} (e : FixedFormulaSubstitution.Environment n depth rawCount)
 (f : Term n) (raw : List.Vector (Program arity) rawCount) (v : List.Vector Nat arity)
 (sigma : Fin rawCount → Term 0)
 (h : ∀ i, evaluate (raw.get i) v = Encodable.encode (GorbowTermPrefixCode.encode (sigma i))) :
 evaluate (.composition (FixedFormulaSubstitution.termProgram e f) raw.get) v =
 Encodable.encode (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (FixedFormulaSubstitution.assignment e sigma) f)) := by
 have hv : (List.Vector.ofFn fun i => evaluate (raw.get i) v) = FixedFormulaSubstitution.rawInputs sigma := by
  ext i
  simpa only [List.Vector.get_ofFn,FixedFormulaSubstitution.rawInputs] using h i
 change evaluate (FixedFormulaSubstitution.termProgram e f) _ = _
 rw [hv,FixedFormulaSubstitution.StatementChecks.exactNativeTerm]

theorem ordinary {arity n rawCount : Nat} (e : FixedFormulaSubstitution.Environment n 1 rawCount)
 (f : Term n) (raw : List.Vector (Program arity) rawCount) (t u code : Program arity) (v : List.Vector Nat arity)
 (F : Term 1) (a b : Term 0)
 (ho : evaluate (.composition (FixedFormulaSubstitution.termProgram e f) raw.get) v = Encodable.encode (GorbowTermPrefixCode.encode F))
 (ht : evaluate t v = Encodable.encode (GorbowTermPrefixCode.encode a))
 (hu : evaluate u v = Encodable.encode (GorbowTermPrefixCode.encode b))
 (hft : evaluate (.composition (FixedFormulaSubstitution.termProgram (UniformRuntimeEnvironmentAgreement.specialize e) f) (t ::ᵥ raw).get) v =
  Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.instantiateTerm F a)))
 (hfu : evaluate (.composition (FixedFormulaSubstitution.termProgram (UniformRuntimeEnvironmentAgreement.specialize e) f) (u ::ᵥ raw).get) v =
  Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.instantiateTerm F b))) :
 evaluate (CurrentCallCongruenceProgram.unary e f raw t u code) v = unaryNumber F a b (evaluate code v) := by
 let ft := Program.composition (FixedFormulaSubstitution.termProgram (UniformRuntimeEnvironmentAgreement.specialize e) f) (t ::ᵥ raw).get
 let fu := Program.composition (FixedFormulaSubstitution.termProgram (UniformRuntimeEnvironmentAgreement.specialize e) f) (u ::ᵥ raw).get
 let openCode := Program.composition (FixedFormulaSubstitution.termProgram e f) raw.get
 let fa := GorbowClosedEquality.instantiateTerm F a
 let fb := GorbowClosedEquality.instantiateTerm F b
 have hQ := equalEval ft ft v fa fa hft hft
 have hR := equalEval ft fu v fa fb hft hfu
 have hmatrix : evaluate (FixedFormulaSubstitution.binary 0 ft openCode) v =
  Encodable.encode (GorbowFormulaPrefixCode.encode (.equal (GorbowClosedEquality.liftClosedTerm 1 fa) F)) := by
  simpa only [GorbowFormulaPrefixCode.encode,PrescribedRuntimeEquality.EncodingProof.liftEncode] using
   binaryEval 0 ft openCode v (GorbowTermPrefixCode.encode fa) (GorbowTermPrefixCode.encode F) hft ho
 change evaluate (CurrentRecursionBaseProgram.mp (FixedFormulaSubstitution.binary 0 ft fu)
  (CurrentRecursionBaseProgram.mp (FixedFormulaSubstitution.binary 7 (FixedFormulaSubstitution.binary 0 ft ft) (FixedFormulaSubstitution.binary 0 ft fu))
   (CurrentRecursionBaseProgram.replacement (FixedFormulaSubstitution.binary 0 ft openCode) t u) code)
  (CurrentRecursionStepProgram.reflexivity ft)) v = _
 rw [mpEval _ _ _ v _ hR,mpEval _ _ _ v _ (impEval _ _ v _ _ hQ hR),
  replacementEval _ _ _ v _ _ _ hmatrix ht hu,CurrentRecursionStepProgram.NativeOperations.reflexivityEval ft v fa hft]
 rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeUnary
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeUnary
