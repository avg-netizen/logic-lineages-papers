module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeCompose
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open HistoryRuleSuffix.NativeProof
open CurrentRecursionStepProgram.NativeOperations CurrentRecursionBaseProgram.TransitivityNativeProof

theorem composeEval {arity : Nat} (p q r hqr hpq : Program arity) (v : List.Vector Nat arity) (P Q R : Formula 0)
 (hp : evaluate p v = Encodable.encode (GorbowFormulaPrefixCode.encode P))
 (hq : evaluate q v = Encodable.encode (GorbowFormulaPrefixCode.encode Q))
 (hr : evaluate r v = Encodable.encode (GorbowFormulaPrefixCode.encode R)) :
 evaluate (compose p q r hqr hpq) v = composeNumber P Q R (evaluate hqr v) (evaluate hpq v) := by
 unfold compose
 rw [mpUnderEval _ _ _ _ _ v P Q R hp hq hr]
 rw [liftEval _ _ _ v (.imp Q R) P (impEval q r v Q R hq hr) hp]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeCompose
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeCompose
