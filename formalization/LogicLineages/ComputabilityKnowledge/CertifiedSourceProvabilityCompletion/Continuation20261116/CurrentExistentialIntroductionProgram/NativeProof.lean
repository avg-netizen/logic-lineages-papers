module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeRule
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentRecursionStepProgram.NativeOperations CurrentRecursionBaseProgram.TransitivityNativeProof CurrentRecursionBaseProgram.NativePrimitives
open NativeSyntax NativeCompose NativeDNE HistoryRuleSuffix.NativeProof
theorem exactNative : Targets.Native := by
 intro a witness code
 let v := Encodable.encode (GorbowFormulaPrefixCode.encode a) ::ᵥ Encodable.encode (GorbowTermPrefixCode.encode witness) ::ᵥ code ::ᵥ nil
 have ha : evaluate (.projection (0 : Fin 3)) v = Encodable.encode (GorbowFormulaPrefixCode.encode a) := rfl
 have ht : evaluate (.projection (1 : Fin 3)) v = Encodable.encode (GorbowTermPrefixCode.encode witness) := rfl
 unfold program
 rw [mpEval _ _ _ v a.ex (exEval _ v a ha),NativeRule.ruleEval _ _ v a witness ha ht]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeProof
