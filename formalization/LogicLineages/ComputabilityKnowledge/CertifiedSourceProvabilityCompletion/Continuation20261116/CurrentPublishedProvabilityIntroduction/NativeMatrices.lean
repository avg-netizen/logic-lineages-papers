module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeInner
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeOuter
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeIntroduction
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeMatrices
open GorbowSyntax GorbowPRProgram List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
attribute [local irreducible] GorbowPRProgram.evaluate
theorem inner (v : List.Vector Nat 7) (u : Term 0)
 (hu : v.get 4 = Encodable.encode (GorbowTermPrefixCode.encode u)) :
 evaluate innerMatrixProgram v = Encodable.encode (GorbowFormulaPrefixCode.encode
  (SyntaxSupport.checkerInner (v.get 0) (v.get 1) (v.get 2) u)) := NativeInner.inner v u hu

theorem outer (v : List.Vector Nat 7) (u : Term 0)
 (hu : v.get 4 = Encodable.encode (GorbowTermPrefixCode.encode u)) :
 evaluate outerMatrixProgram v = Encodable.encode (GorbowFormulaPrefixCode.encode
  (Formula.ex (SyntaxSupport.checkerBody (v.get 0) (v.get 1) u))) := NativeOuter.outer v u hu

theorem introduceEval {n : Nat} (a w code : Program n) (v : List.Vector Nat n)
 (A : Formula 1) (t : Term 0)
 (ha : evaluate a v = Encodable.encode (GorbowFormulaPrefixCode.encode A))
 (hw : evaluate w v = Encodable.encode (GorbowTermPrefixCode.encode t)) :
 evaluate (introduce a w code) v = CurrentExistentialIntroductionProgram.number A t (evaluate code v) := NativeIntroduction.introduceEval a w code v A t ha hw

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeMatrices
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeMatrices
