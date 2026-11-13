module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.NativeProof
open GorbowSyntax GorbowPRProgram List.Vector
open HistoryRuleSuffix.NativeProof

theorem nativeCalibration : Targets.NativeCalibration := by
 intro value
 induction value with
 | zero =>
   change evaluate base nil = _
   rw [base,twoEval,constantEval,constantEval,HistoryCodec.NativeProof.nativeConsAllVectors]
   rfl
 | succ value ih =>
   change evaluate step (value ::ᵥ evaluate numeralCode (value ::ᵥ nil) ::ᵥ nil) = _
   rw [step,twoEval,constantEval,projectionEval]
   change evaluate HistoryCodec.cons (2 ::ᵥ evaluate numeralCode (value ::ᵥ nil) ::ᵥ nil) = _
   rw [ih,HistoryCodec.NativeProof.nativeConsAllVectors]
   rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralNumeralPrefix.NativeProof
