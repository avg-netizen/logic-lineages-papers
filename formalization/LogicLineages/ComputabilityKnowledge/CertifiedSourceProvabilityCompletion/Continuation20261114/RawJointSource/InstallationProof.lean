module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawJointSource.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawJointSource.InstallationProof
open GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- One fixed finite carrier supplies every raw interface node. The verifier
address is the caller's exact installed source address, not a fresh copy. -/
theorem installed (old oldA : Program 1) (x : Program 3)
 (n : Nat) (p : Program n) (tag utag : Nat)
 (h : (nodes p)[tag]? = some ⟨6,ReflexivityInstalled.bundle (items old oldA x)⟩)
 (hu : (nodes p)[utag]? = some ⟨5,ReflexivityFuel.checker old (RawAddZero.arithmeticLeaf oldA) x⟩) :
 (∃ (mtag : Nat), (nodes p)[mtag]? = some (⟨4,LiteralRawMP.constructor⟩ : Packed)) ∧
 ∃ I : RawReflexivityCertificate.Installation p old (RawAddZero.arithmeticLeaf oldA) x,
 ∃ J : RawAddZeroCertificate.Installation p (ReflexivitySource.logical old) oldA x,
 I.utag = utag ∧ J.utag = I.utag ∧ J.ptag = I.ptag ∧ J.ctag = I.ctag ∧
 J.atag = I.atag ∧ J.vtag = I.vtag := by
 obtain ⟨mtag,hm⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨4,LiteralRawMP.constructor⟩ (by simp [items, RawReflexivitySource.items])
 obtain ⟨qtag,hq⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,RawReflexivity.lineConstructor⟩ (by simp [items, RawReflexivitySource.items])
 obtain ⟨ptag,hp⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨2,HistoryCodec.pair⟩ (by simp [items, RawReflexivitySource.items])
 obtain ⟨ctag,hc⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨2,HistoryCodec.cons⟩ (by simp [items, RawReflexivitySource.items])
 obtain ⟨atag,ha⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨2,HistoryAppend.append⟩ (by simp [items, RawReflexivitySource.items])
 obtain ⟨vtag,hv⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ (by simp [items, RawReflexivitySource.items])
 obtain ⟨ftag,hf⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨2,LiteralSyntaxValidator.formulaValidator⟩ (by simp [items, RawReflexivitySource.items])
 obtain ⟨ltag,hl⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,TwoSol20261113.ReflexivityCertificate.validity⟩ (by simp [items, RawReflexivitySource.items])
 obtain ⟨btag,hb⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,TwoSol20261113.ReflexivityCertificate.logical old⟩ (by simp [items, RawReflexivitySource.items])
 obtain ⟨dtag,hd⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨4,TwoSol20261113.ReflexivityCertificate.dispatcher old (RawAddZero.arithmeticLeaf oldA) x⟩ (by simp [items, RawReflexivitySource.items])
 obtain ⟨itag,hi⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨4,SixSol20261112.HistoryMachine.iterator (TwoSol20261113.ReflexivityCertificate.kernel old (RawAddZero.arithmeticLeaf oldA) x)⟩ (by simp [items, RawReflexivitySource.items])
 obtain ⟨qctag,hqc⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨5,TwoSol20261113.ReflexivityCertificate.checker old (RawAddZero.arithmeticLeaf oldA) x⟩ (by simp [items, RawReflexivitySource.items])
 let I : RawReflexivityCertificate.Installation p old (RawAddZero.arithmeticLeaf oldA) x := {
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
 obtain ⟨aqtag,haq⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,RawAddZero.lineConstructor⟩ (by simp [items])
 obtain ⟨abtag,hab⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,RawAddZero.arithmeticLeaf oldA⟩ (by simp [items])
 let J : RawAddZeroCertificate.Installation p (ReflexivitySource.logical old) oldA x := {
  qtag := aqtag
  ptag := ptag
  ctag := ctag
  atag := atag
  vtag := vtag
  ftag := ftag
  ltag := ltag
  btag := abtag
  dtag := dtag
  itag := itag
  qctag := qctag
  utag := utag
  hq := haq
  hp := hp
  hc := hc
  ha := ha
  hv := hv
  hf := hf
  hl := hl
  hb := hab
  hd := hd
  hi := hi
  hqc := hqc
  hu := hu
 }
 exact ⟨⟨mtag,hm⟩,I,J,rfl,rfl,rfl,rfl,rfl,rfl⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawJointSource.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawJointSource.InstallationProof
