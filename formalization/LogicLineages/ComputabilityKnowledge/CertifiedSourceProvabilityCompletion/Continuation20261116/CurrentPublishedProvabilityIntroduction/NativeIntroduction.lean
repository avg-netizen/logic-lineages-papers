module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeEvaluation
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeIntroduction
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115

attribute [local irreducible] GorbowPRProgram.evaluate

theorem introduceEval {n : Nat} (a w code : Program n) (v : List.Vector Nat n)
 (A : Formula 1) (t : Term 0)
 (ha : evaluate a v = Encodable.encode (GorbowFormulaPrefixCode.encode A))
 (hw : evaluate w v = Encodable.encode (GorbowTermPrefixCode.encode t)) :
 evaluate (introduce a w code) v = CurrentExistentialIntroductionProgram.number A t (evaluate code v) := by
 rw [introduce,NativeEvaluation.three,ha,hw]
 exact CurrentExistentialIntroductionProgram.StatementChecks.exactNative A t (evaluate code v)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeIntroduction
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeIntroduction
