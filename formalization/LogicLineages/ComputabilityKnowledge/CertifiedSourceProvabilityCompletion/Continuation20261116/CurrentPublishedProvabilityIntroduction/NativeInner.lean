module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeEvaluation
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeInner
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115

attribute [local irreducible] GorbowPRProgram.evaluate

theorem inner (v : List.Vector Nat 7) (u : Term 0)
 (hu : v.get 4 = Encodable.encode (GorbowTermPrefixCode.encode u)) :
 evaluate innerMatrixProgram v = Encodable.encode (GorbowFormulaPrefixCode.encode
  (SyntaxSupport.checkerInner (v.get 0) (v.get 1) (v.get 2) u)) := by
 rw [innerMatrixProgram,NativeEvaluation.composition,NativeInputs.inner v u hu]
 exact (FixedFormulaSubstitution.StatementChecks.exactNativeFormula 5 1 4 innerEnvironment bodyTemplate (NativeInputs.innerTerms v u)).trans
  (congrArg (fun z => Encodable.encode (GorbowFormulaPrefixCode.encode z)) (TemplateSyntax.inner v u))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeInner
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeInner
