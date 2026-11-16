module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.BundleProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem unpack {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (rawOld ar : Program 1) (baseX : Program 3) (tag : Nat)
 (he : (nodes p)[tag]? = some ⟨6,extra f lhs rhs t rawOld ar baseX⟩) :
 (∃ oldTag : Nat, (nodes p)[oldTag]? = some ⟨6,CurrentNamedAliasCertificate.extra f lhs rhs t rawOld ar baseX⟩) ∧
 Nonempty (ArithmeticTemplateEvaluation.TemplateInstallation p template) := by
 have hall := ReflexivityInstalled.BundleProof.bundleInstallation
  [⟨6,CurrentNamedAliasCertificate.extra f lhs rhs t rawOld ar baseX⟩,
   ⟨2,LiteralTemplateQuote.templateQuote template⟩,
   ⟨2,ArithmeticTemplateEvaluation.valueProgram template⟩,
   ⟨2,ArithmeticTemplateEvaluation.certificateProgram template⟩] n p tag he
 obtain ⟨q,hq⟩ := hall ⟨2,LiteralTemplateQuote.templateQuote template⟩ (by simp)
 obtain ⟨v,hv⟩ := hall ⟨2,ArithmeticTemplateEvaluation.valueProgram template⟩ (by simp)
 obtain ⟨c,hc⟩ := hall ⟨2,ArithmeticTemplateEvaluation.certificateProgram template⟩ (by simp)
 exact ⟨hall _ (by simp),⟨⟨q,v,c,hq,hv,hc⟩⟩⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.BundleProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderCertificate.BundleProof
