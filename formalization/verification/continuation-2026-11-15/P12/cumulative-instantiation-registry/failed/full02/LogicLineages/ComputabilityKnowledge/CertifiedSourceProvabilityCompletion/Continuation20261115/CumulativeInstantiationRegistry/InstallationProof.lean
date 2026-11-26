module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Fields04Proof
public import LogicLineages.ComputabilityKnowledge.GorbowPRRegistryStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.InstallationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem finiteInstallation : Targets.FiniteInstallation := by
 intro lhs rhs k t old a x
 let p := carrier lhs rhs t old a x
 have hall : ∀ q ∈ items lhs rhs t old a x, ∃ tag : Nat, (nodes p)[tag]? = some q :=
  ReflexivityInstalled.BundleProof.bundleInstallation (items lhs rhs t old a x) 6 p 0
   (GorbowPRRegistry.StatementChecks.rootTag 6 p)
 obtain ⟨previous⟩ := Items_RawUniversalCongruence.installed old a x p (fun q hq => hall q (by
  simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨current⟩ := Items_RawEqualityInstantiationCertificate.installed lhs rhs (previousLogical old) (RawMulNewestAddition.arithmetic a) x p (fun q hq => hall q (by
  simp only [items,List.mem_append]; exact Or.inr (Or.inl hq)))
 obtain ⟨quoteTag,hquote⟩ := hall (⟨k,LiteralTemplateQuote.templateQuote t⟩ : Packed) (by simp [items])
 obtain ⟨valueTag,hvalue⟩ := hall (⟨k,ArithmeticTemplateEvaluation.valueProgram t⟩ : Packed) (by simp [items])
 obtain ⟨certificateTag,hcertificate⟩ := hall (⟨k,ArithmeticTemplateEvaluation.certificateProgram t⟩ : Packed) (by simp [items])
 let template : ArithmeticTemplateEvaluation.TemplateInstallation p t := {quoteTag,valueTag,certificateTag,hquote,hvalue,hcertificate}
 exact ⟨{previous,template,current}⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.InstallationProof
