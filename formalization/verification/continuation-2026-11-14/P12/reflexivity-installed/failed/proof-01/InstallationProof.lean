module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.BundleProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.InstallationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
/-- All interface slots are obtained as literal bundle descendants. No acceptance premise. -/
theorem installed (k : Nat) (t : Term k) (old a : Program 1) (x : Program 3)
 (n : Nat) (p : Program n) (tag : Nat)
 (h : (nodes p)[tag]? = some ⟨6,bundle (items t old a x)⟩) :
 (∃ mtag, (nodes p)[mtag]? = some ⟨4,LiteralRawMP.constructor⟩) ∧
 Nonempty (TwoSol20261113.ReflexivityCertificate.Installation p t old a x) := by
 obtain ⟨mtag,hm⟩ := BundleProof.bundleInstallation (items t old a x) n p tag h
  ⟨4,LiteralRawMP.constructor⟩ (by simp [items])
 obtain ⟨qtag,hq⟩ := BundleProof.bundleInstallation (items t old a x) n p tag h
  ⟨k,LiteralReflexivityQuote.lineQuote t⟩ (by simp [items])
 obtain ⟨etag,he⟩ := BundleProof.bundleInstallation (items t old a x) n p tag h
  ⟨k,LiteralEqualityQuote.equalityQuote t t⟩ (by simp [items])
 obtain ⟨ttag,ht⟩ := BundleProof.bundleInstallation (items t old a x) n p tag h
  ⟨k,LiteralTemplateQuote.templateQuote t⟩ (by simp [items])
 obtain ⟨ptag,hp⟩ := BundleProof.bundleInstallation (items t old a x) n p tag h
  ⟨2,HistoryCodec.pair⟩ (by simp [items])
 obtain ⟨ctag,hc⟩ := BundleProof.bundleInstallation (items t old a x) n p tag h
  ⟨2,HistoryCodec.cons⟩ (by simp [items])
 obtain ⟨atag,ha⟩ := BundleProof.bundleInstallation (items t old a x) n p tag h
  ⟨2,HistoryAppend.append⟩ (by simp [items])
 obtain ⟨vtag,hv⟩ := BundleProof.bundleInstallation (items t old a x) n p tag h
  ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ (by simp [items])
 obtain ⟨ftag,hf⟩ := BundleProof.bundleInstallation (items t old a x) n p tag h
  ⟨2,LiteralSyntaxValidator.formulaValidator⟩ (by simp [items])
 obtain ⟨ltag,hl⟩ := BundleProof.bundleInstallation (items t old a x) n p tag h
  ⟨1,TwoSol20261113.ReflexivityCertificate.validity⟩ (by simp [items])
 obtain ⟨btag,hb⟩ := BundleProof.bundleInstallation (items t old a x) n p tag h
  ⟨1,TwoSol20261113.ReflexivityCertificate.logical old⟩ (by simp [items])
 obtain ⟨dtag,hd⟩ := BundleProof.bundleInstallation (items t old a x) n p tag h
  ⟨4,TwoSol20261113.ReflexivityCertificate.dispatcher old a x⟩ (by simp [items])
 obtain ⟨itag,hi⟩ := BundleProof.bundleInstallation (items t old a x) n p tag h
  ⟨4,SixSol20261112.HistoryMachine.iterator (TwoSol20261113.ReflexivityCertificate.kernel old a x)⟩ (by simp [items])
 obtain ⟨qctag,hqc⟩ := BundleProof.bundleInstallation (items t old a x) n p tag h
  ⟨5,TwoSol20261113.ReflexivityCertificate.checker old a x⟩ (by simp [items])
 exact ⟨⟨mtag,hm⟩,⟨{ qtag := qtag, etag := etag, ttag := ttag, ptag := ptag, ctag := ctag, atag := atag, vtag := vtag, ftag := ftag, ltag := ltag, btag := btag, dtag := dtag, itag := itag, qctag := qctag,
  hq := hq, he := he, ht := ht, hp := hp, hc := hc, ha := ha, hv := hv, hf := hf, hl := hl, hb := hb, hd := hd, hi := hi, hqc := hqc }⟩⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.InstallationProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.InstallationProof.installed
