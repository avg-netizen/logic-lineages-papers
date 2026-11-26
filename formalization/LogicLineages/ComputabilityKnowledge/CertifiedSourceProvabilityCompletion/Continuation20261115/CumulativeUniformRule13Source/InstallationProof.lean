module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Source.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Source.InstallationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem installed (f : Formula 1) (lhs rhs : Term 1) {k : Nat} (t : Term k) (old a : Program 1) (baseX : Program 3)
 (pF pR : Program 1) (etag : Nat)
 (he : (nodes (root f lhs rhs pF pR old a baseX))[etag]? = some ⟨6,extra f lhs rhs t old a baseX⟩) :
 ∃ (mtag btag : Nat),
 ∃ I : CumulativeUniformRule13Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 I.current.verifierTag = GorbowNamedInternalProvability.checkerTag pF ∧
 (nodes (root f lhs rhs pF pR old a baseX))[btag]? =
  some ⟨6,CumulativeUniformRule13Registry.carrier f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)⟩ ∧
 (nodes (root f lhs rhs pF pR old a baseX))[mtag]? = some ⟨4,LiteralRawMP.constructor⟩ := by
 let p := root f lhs rhs pF pR old a baseX
 let x := SaturatedAxiomLeaf.saturated baseX
 have hextra := ReflexivityInstalled.BundleProof.bundleInstallation
  [⟨4,LiteralRawMP.constructor⟩,⟨6,CumulativeUniformRule13Registry.carrier f lhs rhs t old a x⟩] 4 p etag he
 obtain ⟨mtag,hm⟩ := hextra ⟨4,LiteralRawMP.constructor⟩ (by simp)
 obtain ⟨btag,hb⟩ := hextra ⟨6,CumulativeUniformRule13Registry.carrier f lhs rhs t old a x⟩ (by simp)
 have hall : ∀ q ∈ CumulativeUniformRule13Registry.items f lhs rhs t old a x,
  ∃ tag : Nat, (nodes p)[tag]? = some q :=
  ReflexivityInstalled.BundleProof.bundleInstallation (CumulativeUniformRule13Registry.items f lhs rhs t old a x) 4 p btag hb
 obtain ⟨J⟩ := CumulativeUniformRule13Registry.InstallationProof.installed p f lhs rhs t old a x hall
 have hu : (nodes p)[GorbowNamedInternalProvability.checkerTag pF]? =
  some ⟨5,verifier f lhs rhs old a baseX⟩ :=
  GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR (verifier f lhs rhs old a baseX)
 let namedCurrent : UniformClosedRule13Certificate.Installation p
  (CumulativeUniformRule13Registry.previousLogical f lhs rhs old) (RawMulNewestAddition.arithmetic a) x :=
  {J.current with verifierTag := GorbowNamedInternalProvability.checkerTag pF, h_verifier := hu}
 exact ⟨mtag,btag,{previous := J.previous,current := namedCurrent},rfl,hb,hm⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Source.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Source.InstallationProof
