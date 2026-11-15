module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationSource.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.StatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationSource.InstallationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem installed (lhs rhs : Term 1) {k : Nat} (t : Term k) (old a : Program 1) (baseX : Program 3)
 (pF pR : Program 1) (etag : Nat)
 (he : (nodes (root lhs rhs pF pR old a baseX))[etag]? = some ⟨6,extra lhs rhs t old a baseX⟩) :
 ∃ (mtag btag : Nat),
 ∃ I : CumulativeInstantiationRegistry.JointInstallation (root lhs rhs pF pR old a baseX)
  lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 I.current.utag = GorbowNamedInternalProvability.checkerTag pF ∧
 (nodes (root lhs rhs pF pR old a baseX))[btag]? =
  some ⟨6,CumulativeInstantiationRegistry.carrier lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)⟩ ∧
 (nodes (root lhs rhs pF pR old a baseX))[mtag]? = some ⟨4,LiteralRawMP.constructor⟩ := by
 let p := root lhs rhs pF pR old a baseX
 let x := SaturatedAxiomLeaf.saturated baseX
 have hextra := ReflexivityInstalled.BundleProof.bundleInstallation
  [⟨4,LiteralRawMP.constructor⟩,⟨6,CumulativeInstantiationRegistry.carrier lhs rhs t old a x⟩] 4 p etag he
 obtain ⟨mtag,hm⟩ := hextra ⟨4,LiteralRawMP.constructor⟩ (by simp)
 obtain ⟨btag,hb⟩ := hextra ⟨6,CumulativeInstantiationRegistry.carrier lhs rhs t old a x⟩ (by simp)
 have hall : ∀ q ∈ CumulativeInstantiationRegistry.items lhs rhs t old a x,
  ∃ tag : Nat, (nodes p)[tag]? = some q :=
  ReflexivityInstalled.BundleProof.bundleInstallation (CumulativeInstantiationRegistry.items lhs rhs t old a x) 4 p btag hb
 obtain ⟨previous⟩ := CumulativeInstantiationRegistry.Items_RawUniversalCongruence.installed old a x p
  (fun q hq => hall q (by simp only [CumulativeInstantiationRegistry.items,List.mem_append]; exact Or.inl (Or.inl hq)))
 obtain ⟨current⟩ := CumulativeInstantiationRegistry.Items_RawEqualityInstantiationCertificate.installed
  lhs rhs (CumulativeInstantiationRegistry.previousLogical old) (RawMulNewestAddition.arithmetic a) x p
  (fun q hq => hall q (by simp only [CumulativeInstantiationRegistry.items,List.mem_append]; exact Or.inl (Or.inr hq)))
 obtain ⟨quoteTag,hquote⟩ := hall (⟨k,LiteralTemplateQuote.templateQuote t⟩ : Packed) (by simp [CumulativeInstantiationRegistry.items])
 obtain ⟨valueTag,hvalue⟩ := hall (⟨k,ArithmeticTemplateEvaluation.valueProgram t⟩ : Packed) (by simp [CumulativeInstantiationRegistry.items])
 obtain ⟨certificateTag,hcertificate⟩ := hall (⟨k,ArithmeticTemplateEvaluation.certificateProgram t⟩ : Packed) (by simp [CumulativeInstantiationRegistry.items])
 let template : ArithmeticTemplateEvaluation.TemplateInstallation p t := {quoteTag,valueTag,certificateTag,hquote,hvalue,hcertificate}
 have hu : (nodes p)[GorbowNamedInternalProvability.checkerTag pF]? =
  some ⟨5,verifier lhs rhs old a baseX⟩ :=
  GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR (verifier lhs rhs old a baseX)
 let namedCurrent : RawEqualityInstantiationCertificate.Installation p lhs rhs
  (CumulativeInstantiationRegistry.previousLogical old) (RawMulNewestAddition.arithmetic a) x :=
  {current with utag := GorbowNamedInternalProvability.checkerTag pF, hu := hu}
 exact ⟨mtag,btag,{previous,template,current := namedCurrent},rfl,hb,hm⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationSource.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationSource.InstallationProof
