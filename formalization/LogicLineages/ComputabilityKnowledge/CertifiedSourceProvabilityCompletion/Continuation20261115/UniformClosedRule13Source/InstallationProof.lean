module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source.InstallationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- The installed carrier's tags are recovered anew in the ACTUAL root. -/
theorem installed (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (etag : Nat)
 (he : (nodes (root pF pR old a baseX))[etag]? = some ⟨6,extra old a baseX⟩) :
 ∃ (mtag btag : Nat),
 ∃ I : UniformClosedRule13Certificate.Installation (root pF pR old a baseX) old a (SaturatedAxiomLeaf.saturated baseX),
 I.verifierTag = GorbowNamedInternalProvability.checkerTag pF ∧
 (nodes (root pF pR old a baseX))[btag]? = some ⟨6,UniformClosedRule13Registry.carrier old a (SaturatedAxiomLeaf.saturated baseX)⟩ ∧
 (nodes (root pF pR old a baseX))[mtag]? = some ⟨4,LiteralRawMP.constructor⟩ := by
 let p := root pF pR old a baseX
 let x := SaturatedAxiomLeaf.saturated baseX
 have hextra := ReflexivityInstalled.BundleProof.bundleInstallation
  [⟨4,LiteralRawMP.constructor⟩,⟨6,UniformClosedRule13Registry.carrier old a x⟩] 4 p etag he
 obtain ⟨mtag,hm⟩ := hextra ⟨4,LiteralRawMP.constructor⟩ (by simp)
 obtain ⟨btag,hb⟩ := hextra ⟨6,UniformClosedRule13Registry.carrier old a x⟩ (by simp)
 obtain ⟨J⟩ := UniformClosedRule13Registry.InstallationProof.installedAt old a x p btag hb
 have hu : (nodes p)[GorbowNamedInternalProvability.checkerTag pF]? = some ⟨5,verifier old a baseX⟩ :=
  GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR (verifier old a baseX)
 let I : UniformClosedRule13Certificate.Installation p old a x :=
  { J with verifierTag := GorbowNamedInternalProvability.checkerTag pF, h_verifier := hu }
 exact ⟨mtag,btag,I,rfl,hb,hm⟩
/-- Only the ACTUAL root's defining-equation theory is included into S. -/
theorem runtime (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : UniformClosedRule13Certificate.Installation (root pF pR old a baseX) old a (SaturatedAxiomLeaf.saturated baseX)) :
 RuntimeCapability old a baseX pF pR I := by
 intro ctx formula replacement index fuel
 apply GorbowTheoryProofProof.monotonicity _ _
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs))
 exact UniformClosedRule13Certificate.StatementChecks.exactCertificate 4 (root pF pR old a baseX)
  old a (SaturatedAxiomLeaf.saturated baseX) I ctx formula replacement index fuel
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source.InstallationProof
