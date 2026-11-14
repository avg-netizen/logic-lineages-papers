module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivitySource.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivitySource.InstallationProof
open GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- One fixed finite carrier supplies every raw interface node. The verifier
address is the caller's exact installed source address, not a fresh copy. -/
theorem installed (old a : Program 1) (x : Program 3)
 (n : Nat) (p : Program n) (tag utag : Nat)
 (h : (nodes p)[tag]? = some ⟨6,ReflexivityInstalled.bundle (items old a x)⟩)
 (hu : (nodes p)[utag]? = some ⟨5,ReflexivityFuel.checker old a x⟩) :
 (∃ (mtag : Nat), (nodes p)[mtag]? = some (⟨4,LiteralRawMP.constructor⟩ : Packed)) ∧
 ∃ I : RawReflexivityCertificate.Installation p old a x, I.utag = utag := by
 obtain ⟨mtag,hm⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old a x) n p tag h
  ⟨4,LiteralRawMP.constructor⟩ (by simp [items])
 obtain ⟨qtag,hq⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old a x) n p tag h
  ⟨1,RawReflexivity.lineConstructor⟩ (by simp [items])
 obtain ⟨ptag,hp⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old a x) n p tag h
  ⟨2,HistoryCodec.pair⟩ (by simp [items])
 obtain ⟨ctag,hc⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old a x) n p tag h
  ⟨2,HistoryCodec.cons⟩ (by simp [items])
 obtain ⟨atag,ha⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old a x) n p tag h
  ⟨2,HistoryAppend.append⟩ (by simp [items])
 obtain ⟨vtag,hv⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old a x) n p tag h
  ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ (by simp [items])
 obtain ⟨ftag,hf⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old a x) n p tag h
  ⟨2,LiteralSyntaxValidator.formulaValidator⟩ (by simp [items])
 obtain ⟨ltag,hl⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old a x) n p tag h
  ⟨1,TwoSol20261113.ReflexivityCertificate.validity⟩ (by simp [items])
 obtain ⟨btag,hb⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old a x) n p tag h
  ⟨1,TwoSol20261113.ReflexivityCertificate.logical old⟩ (by simp [items])
 obtain ⟨dtag,hd⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old a x) n p tag h
  ⟨4,TwoSol20261113.ReflexivityCertificate.dispatcher old a x⟩ (by simp [items])
 obtain ⟨itag,hi⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old a x) n p tag h
  ⟨4,SixSol20261112.HistoryMachine.iterator (TwoSol20261113.ReflexivityCertificate.kernel old a x)⟩ (by simp [items])
 obtain ⟨qctag,hqc⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old a x) n p tag h
  ⟨5,TwoSol20261113.ReflexivityCertificate.checker old a x⟩ (by simp [items])
 let I : RawReflexivityCertificate.Installation p old a x := {
  qtag := qtag
  ptag := ptag
  ctag := ctag
  atag := atag
  vtag := vtag
  ftag := ftag
  ltag := ltag
  btag := btag
  dtag := dtag
  itag := itag
  qctag := qctag
  utag := utag
  hq := hq
  hp := hp
  hc := hc
  ha := ha
  hv := hv
  hf := hf
  hl := hl
  hb := hb
  hd := hd
  hi := hi
  hqc := hqc
  hu := hu
 }
 exact ⟨⟨mtag,hm⟩,I,rfl⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivitySource.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivitySource.InstallationProof
