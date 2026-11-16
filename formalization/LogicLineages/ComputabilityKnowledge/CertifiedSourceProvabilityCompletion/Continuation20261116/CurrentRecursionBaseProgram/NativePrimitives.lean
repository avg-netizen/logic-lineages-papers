module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.NativePrimitives
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open HistoryRuleSuffix.NativeProof GorbowFormulaSubstitution PrescribedRuntimeEquality

theorem quoteEval {n arity : Nat} (f : Formula n) (raw : Fin n → Program arity) (v : List.Vector Nat arity)
 (sigma : Fin n → Term 0) (h : ∀ i, evaluate (raw i) v = Encodable.encode (GorbowTermPrefixCode.encode (sigma i))) :
 evaluate (quote f raw) v = Encodable.encode (GorbowFormulaPrefixCode.encode (substituteFormula sigma f)) := by
 have hv : (List.Vector.ofFn fun i => evaluate (raw i) v) = FixedFormulaSubstitution.rawInputs sigma := by
  ext i
  simpa only [List.Vector.get_ofFn,FixedFormulaSubstitution.rawInputs] using h i
 change evaluate (FixedFormulaSubstitution.formulaProgram f _) _ = _
 rw [hv,FixedFormulaSubstitution.StatementChecks.exactNativeFormula,PrescribedRuntimeSpecialization.TraceSupportProof.assignmentRuntime]

theorem headQuoteEval {n arity : Nat} (f : Formula (n+1)) (raw : Fin n → Program arity) (v : List.Vector Nat arity)
 (sigma : Fin n → Term 0) (h : ∀ i, evaluate (raw i) v = Encodable.encode (GorbowTermPrefixCode.encode (sigma i))) :
 evaluate (headQuote f raw) v = Encodable.encode (GorbowFormulaPrefixCode.encode (substituteFormula (liftSubstitute sigma) f)) := by
 have hv : (List.Vector.ofFn fun i => evaluate (raw i) v) = FixedFormulaSubstitution.rawInputs sigma := by
  ext i
  simpa only [List.Vector.get_ofFn,FixedFormulaSubstitution.rawInputs] using h i
 change evaluate (FixedFormulaSubstitution.formulaProgram f _) _ = _
 rw [hv,FixedFormulaSubstitution.StatementChecks.exactNativeFormula,PrescribedRuntimeSpecialization.TraceSupportProof.assignmentHead]

theorem consEval (a b : Nat) : evaluate HistoryCodec.cons (a ::ᵥ b ::ᵥ nil) = (Nat.pair a b).succ :=
 HistoryCodec.NativeProof.nativeConsAllVectors _

theorem singletonEval {arity : Nat} (line : Program arity) (v : List.Vector Nat arity) (l : GorbowProofChecker.Line)
 (hl : evaluate line v = Encodable.encode l) :
 evaluate (singleton line) v = GorbowNumericCertificate.certificateNumber [l] := by
 simp only [singleton,twoEval,constantEval,hl,consEval]
 rfl

theorem mpEval {arity : Nat} (formula imp ant : Program arity) (v : List.Vector Nat arity) (f : Formula 0)
 (hf : evaluate formula v = Encodable.encode (GorbowFormulaPrefixCode.encode f)) :
 evaluate (mp formula imp ant) v = GorbowTheoryCertificateOperations.mpCertificate 0
  (GorbowSortedSyntaxCode.formulaCode f) (evaluate imp v) (evaluate ant v) := by
 change evaluate LiteralRawMP.constructor (0 ::ᵥ evaluate formula v ::ᵥ evaluate imp v ::ᵥ evaluate ant v ::ᵥ nil) = _
 rw [hf,LiteralRawMP.StatementChecks.exactNativeEven]
 rfl

theorem allInstanceEval {arity : Nat} (matrix replacement : Program arity) (v : List.Vector Nat arity)
 (f : Formula 1) (t : Term 0)
 (hf : evaluate matrix v = Encodable.encode (GorbowFormulaPrefixCode.encode f))
 (ht : evaluate replacement v = Encodable.encode (GorbowTermPrefixCode.encode t)) :
 evaluate (allInstance matrix replacement) v = GorbowNumericCertificate.certificateNumber [GorbowProofChecker.logicalLine (.allInstantiate f t)] := by
 apply singletonEval
 change evaluate UniformClosedRule13.lineConstructor (evaluate matrix v ::ᵥ evaluate replacement v ::ᵥ nil) = _
 rw [hf,ht,UniformClosedRule13.StatementChecks.exactNativeLine,PrescribedRuntimeSpecialization.PrimitiveProof.nativeLine]

theorem replacementEval {arity : Nat} (matrix left right : Program arity) (v : List.Vector Nat arity)
 (f : Formula 1) (t u : Term 0)
 (hf : evaluate matrix v = Encodable.encode (GorbowFormulaPrefixCode.encode f))
 (ht : evaluate left v = Encodable.encode (GorbowTermPrefixCode.encode t))
 (hu : evaluate right v = Encodable.encode (GorbowTermPrefixCode.encode u)) :
 evaluate (replacement matrix left right) v = GorbowNumericCertificate.certificateNumber [GorbowProofChecker.logicalLine (.equalityReplace f t u)] := by
 apply singletonEval
 change evaluate UniformClosedRule12.lineConstructor (evaluate matrix v ::ᵥ evaluate left v ::ᵥ evaluate right v ::ᵥ nil) = _
 rw [hf,ht,hu,UniformClosedRule12.StatementChecks.exactNativeLine,PrescribedRuntimeEquality.PrimitiveProof.nativeReplacement]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.NativePrimitives
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.NativePrimitives
