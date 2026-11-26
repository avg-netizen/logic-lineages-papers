module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaRegistry.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaRegistry.InstallationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Rebuild every installation at the actual supplied root from its own
structural item memberships. No old carrier tags or Theory inclusion are used. -/
theorem installed {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3)
 (hall : ∀ q ∈ items f lhs rhs t old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (JointInstallation p f lhs rhs t old a x) := by
 have hold : ∀ q ∈ CumulativeInstantiationRegistry.items lhs rhs t old a x,
  ∃ tag : Nat, (nodes p)[tag]? = some q := fun q hq => hall q (by
   simp only [items,List.mem_append]; exact Or.inl hq)
 obtain ⟨base⟩ := CumulativeInstantiationRegistry.Items_RawUniversalCongruence.installed old a x p (fun q hq => hold q (by
  simp only [CumulativeInstantiationRegistry.items,List.mem_append]; exact Or.inl (Or.inl hq)))
 obtain ⟨equality⟩ := CumulativeInstantiationRegistry.Items_RawEqualityInstantiationCertificate.installed lhs rhs
  (CumulativeInstantiationRegistry.previousLogical old) (RawMulNewestAddition.arithmetic a) x p (fun q hq => hold q (by
   simp only [CumulativeInstantiationRegistry.items,List.mem_append]; exact Or.inl (Or.inr hq)))
 obtain ⟨quoteTag,hquote⟩ := hold (⟨k,LiteralTemplateQuote.templateQuote t⟩ : Packed) (by simp [CumulativeInstantiationRegistry.items])
 obtain ⟨valueTag,hvalue⟩ := hold (⟨k,ArithmeticTemplateEvaluation.valueProgram t⟩ : Packed) (by simp [CumulativeInstantiationRegistry.items])
 obtain ⟨certificateTag,hcertificate⟩ := hold (⟨k,ArithmeticTemplateEvaluation.certificateProgram t⟩ : Packed) (by simp [CumulativeInstantiationRegistry.items])
 let template : ArithmeticTemplateEvaluation.TemplateInstallation p t := {quoteTag,valueTag,certificateTag,hquote,hvalue,hcertificate}
 let previous : CumulativeInstantiationRegistry.JointInstallation p lhs rhs t old a x :=
  {previous := base, template, current := equality}
 obtain ⟨current⟩ := FullFormulaInstantiationRegistry.Proof.installed f (previousLogical lhs rhs old)
  (RawMulNewestAddition.arithmetic a) x p (fun q hq => hall q (by
   simp only [items,List.mem_append]; exact Or.inr hq))
 exact ⟨{previous,current}⟩
theorem finiteInstallation : Targets.FiniteInstallation := by
 intro f lhs rhs k t old a x
 let p := carrier f lhs rhs t old a x
 have hall : ∀ q ∈ items f lhs rhs t old a x, ∃ tag : Nat, (nodes p)[tag]? = some q :=
  ReflexivityInstalled.BundleProof.bundleInstallation (items f lhs rhs t old a x) 6 p 0
   (GorbowPRRegistry.StatementChecks.rootTag 6 p)
 exact installed p f lhs rhs t old a x hall
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaRegistry.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaRegistry.InstallationProof
