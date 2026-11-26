module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeEvaluation
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeOuter
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115

attribute [local irreducible] GorbowPRProgram.evaluate

theorem outer (v : List.Vector Nat 7) (u : Term 0)
 (hu : v.get 4 = Encodable.encode (GorbowTermPrefixCode.encode u)) :
 evaluate outerMatrixProgram v = Encodable.encode (GorbowFormulaPrefixCode.encode
  (Formula.ex (SyntaxSupport.checkerBody (v.get 0) (v.get 1) u))) := by
 rw [outerMatrixProgram,NativeEvaluation.composition,NativeInputs.outer v u hu]
 exact (FixedFormulaSubstitution.StatementChecks.exactNativeFormula 4 1 3 outerEnvironment (.ex bodyTemplate) (NativeInputs.outerTerms v u)).trans
  (congrArg (fun z => Encodable.encode (GorbowFormulaPrefixCode.encode z)) (TemplateSyntax.outer v u))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeOuter
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeOuter
