module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.RegistryInstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.InstallationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem installed (f : Formula 1) (lhs rhs : Term 1) {k : Nat} (t : Term k) (old a : Program 1) (baseX : Program 3)
 (pF pR : Program 1) (etag : Nat)
 (he : (nodes (root f lhs rhs pF pR old a baseX))[etag]? = some ⟨6,extra f lhs rhs t old a baseX⟩) :
 ∃ (mtag btag : Nat),
 ∃ I : JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 I.currentK.verifierTag = GorbowNamedInternalProvability.checkerTag pF ∧
 I.currentS.verifierTag = GorbowNamedInternalProvability.checkerTag pF ∧
 I.currentK.coreTag = I.currentS.coreTag ∧
 I.currentK.iteratorTag = I.currentS.iteratorTag ∧
 (nodes (root f lhs rhs pF pR old a baseX))[btag]? =
  some ⟨6,carrier f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)⟩ ∧
 (nodes (root f lhs rhs pF pR old a baseX))[mtag]? = some ⟨4,LiteralRawMP.constructor⟩ := by
 let p := root f lhs rhs pF pR old a baseX
 let x := SaturatedAxiomLeaf.saturated baseX
 have hextra := ReflexivityInstalled.BundleProof.bundleInstallation
  [⟨4,LiteralRawMP.constructor⟩,⟨6,carrier f lhs rhs t old a x⟩] 4 p etag he
 obtain ⟨mtag,hm⟩ := hextra ⟨4,LiteralRawMP.constructor⟩ (by simp)
 obtain ⟨btag,hb⟩ := hextra ⟨6,carrier f lhs rhs t old a x⟩ (by simp)
 have hall : ∀ q ∈ items f lhs rhs t old a x,
  ∃ tag : Nat, (nodes p)[tag]? = some q :=
  ReflexivityInstalled.BundleProof.bundleInstallation (items f lhs rhs t old a x) 4 p btag hb
 obtain ⟨J,hcore,hiterator⟩ := RegistryInstallationProof.installed p f lhs rhs t old a x hall
 have hu : (nodes p)[GorbowNamedInternalProvability.checkerTag pF]? =
  some ⟨5,verifier f lhs rhs old a baseX⟩ :=
  GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR (verifier f lhs rhs old a baseX)
 let namedK : UniformClosedPropositionalCertificate.Installation p
  (previousLogical f lhs rhs old) (arithmetic a) x false :=
  {J.currentK with verifierTag := GorbowNamedInternalProvability.checkerTag pF, h_verifierTag := hu}
 let namedS : UniformClosedPropositionalCertificate.Installation p
  (previousLogical f lhs rhs old) (arithmetic a) x true :=
  {J.currentS with verifierTag := GorbowNamedInternalProvability.checkerTag pF, h_verifierTag := hu}
 exact ⟨mtag,btag,{previous := J.previous,currentK := namedK,currentS := namedS},rfl,rfl,hcore,hiterator,hb,hm⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.InstallationProof
