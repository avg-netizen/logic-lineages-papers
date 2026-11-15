module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaSource.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaSource.InstallationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem installed (f : Formula 1) (lhs rhs : Term 1) {k : Nat} (t : Term k) (old a : Program 1) (baseX : Program 3)
 (pF pR : Program 1) (etag : Nat)
 (he : (nodes (root f lhs rhs pF pR old a baseX))[etag]? = some ⟨6,extra f lhs rhs t old a baseX⟩) :
 ∃ (mtag btag : Nat),
 ∃ I : CumulativeFullFormulaRegistry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 I.current.utag = GorbowNamedInternalProvability.checkerTag pF ∧
 (nodes (root f lhs rhs pF pR old a baseX))[btag]? =
  some ⟨6,CumulativeFullFormulaRegistry.carrier f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)⟩ ∧
 (nodes (root f lhs rhs pF pR old a baseX))[mtag]? = some ⟨4,LiteralRawMP.constructor⟩ := by
 let p := root f lhs rhs pF pR old a baseX
 let x := SaturatedAxiomLeaf.saturated baseX
 have hextra := ReflexivityInstalled.BundleProof.bundleInstallation
  [⟨4,LiteralRawMP.constructor⟩,⟨6,CumulativeFullFormulaRegistry.carrier f lhs rhs t old a x⟩] 4 p etag he
 obtain ⟨mtag,hm⟩ := hextra ⟨4,LiteralRawMP.constructor⟩ (by simp)
 obtain ⟨btag,hb⟩ := hextra ⟨6,CumulativeFullFormulaRegistry.carrier f lhs rhs t old a x⟩ (by simp)
 have hall : ∀ q ∈ CumulativeFullFormulaRegistry.items f lhs rhs t old a x,
  ∃ tag : Nat, (nodes p)[tag]? = some q :=
  ReflexivityInstalled.BundleProof.bundleInstallation (CumulativeFullFormulaRegistry.items f lhs rhs t old a x) 4 p btag hb
 obtain ⟨J⟩ := CumulativeFullFormulaRegistry.InstallationProof.installed p f lhs rhs t old a x hall
 have hu : (nodes p)[GorbowNamedInternalProvability.checkerTag pF]? =
  some ⟨5,verifier f lhs rhs old a baseX⟩ :=
  GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR (verifier f lhs rhs old a baseX)
 let namedCurrent : FullFormulaInstantiationCertificate.Installation p f
  (CumulativeFullFormulaRegistry.previousLogical lhs rhs old) (RawMulNewestAddition.arithmetic a) x :=
  {J.current with utag := GorbowNamedInternalProvability.checkerTag pF, hu := hu}
 exact ⟨mtag,btag,{previous := J.previous,current := namedCurrent},rfl,hb,hm⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaSource.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeFullFormulaSource.InstallationProof
