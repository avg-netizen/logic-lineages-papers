module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.InstallationProof
open GorbowPRProgram GorbowPRRegistry SixSol20261113
theorem installed (old oldA : Program 1) (x : Program 3) (n : Nat) (p : Program n) (tag utag : Nat)
 (h : (nodes p)[tag]? = some ⟨6,ReflexivityInstalled.bundle (items old oldA x)⟩)
 (hu : (nodes p)[utag]? = some ⟨5,RawRightReplaceCertificate.verifier (RawCumulativeLogical.logical old) (arithmetic oldA) x⟩) :
 ∃ I : RawAdditionIteration.Installation p old oldA x, I.utag = utag := by
 obtain ⟨mpTag,hmp⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨4,LiteralRawMP.constructor⟩ (by simp [items])
 obtain ⟨reflexivityTag,hreflexivity⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,RawReflexivity.lineConstructor⟩ (by simp [items])
 obtain ⟨zeroTag,hzero⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,RawAddZero.lineConstructor⟩ (by simp [items])
 obtain ⟨addTag,hadd⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨2,RawAddSucc.lineConstructor⟩ (by simp [items])
 obtain ⟨replaceTag,hreplace⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨2,RawSuccReplace.lineConstructor⟩ (by simp [items])
 obtain ⟨ptag,hp⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨2,HistoryCodec.pair⟩ (by simp [items])
 obtain ⟨ctag,hc⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨2,HistoryCodec.cons⟩ (by simp [items])
 obtain ⟨atag,ha⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨2,HistoryAppend.append⟩ (by simp [items])
 obtain ⟨vtag,hv⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ (by simp [items])
 obtain ⟨ftag,hf⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨2,LiteralSyntaxValidator.formulaValidator⟩ (by simp [items])
 obtain ⟨ltag,hl⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,LiteralSyntaxValidator.lineValidator⟩ (by simp [items])
 obtain ⟨btag,hb⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,logical old⟩ (by simp [items])
 obtain ⟨arithmeticTag,harithmetic⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,arithmetic oldA⟩ (by simp [items])
 obtain ⟨dtag,hd⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨4,RawRightReplaceDispatcher.dispatcher (RawCumulativeLogical.logical old) (arithmetic oldA) x⟩ (by simp [items])
 obtain ⟨itag,hi⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨4,SixSol20261112.HistoryMachine.iterator (RawRightReplaceCertificate.kernel (RawCumulativeLogical.logical old) (arithmetic oldA) x)⟩ (by simp [items])
 obtain ⟨qctag,hqc⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨5,RawRightReplaceCertificate.checker (RawCumulativeLogical.logical old) (arithmetic oldA) x⟩ (by simp [items])
 obtain ⟨lengthTag,hlength⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,HistoryLengthOffset.lengthProgram⟩ (by simp [items])
 obtain ⟨rightTag,hright⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,HistoryDecoder.decoder true⟩ (by simp [items])
 obtain ⟨dropTag,hdrop⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨2,HistoryLookup.drop⟩ (by simp [items])
 obtain ⟨lookupTag,hlookup⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨2,HistoryLookup.lookup⟩ (by simp [items])
 obtain ⟨qtag,hq⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨3,RawRightReplace.lineConstructor⟩ (by simp [items])
 obtain ⟨oldTag,hold⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,RawCumulativeLogical.logical old⟩ (by simp [items])
 obtain ⟨leftTag,hleft⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,HistoryDecoder.decoder false⟩ (by simp [items])
 obtain ⟨baseTag,hbase⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,RawAdditionIteration.base⟩ (by simp [items])
 obtain ⟨stepTag,hstep⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨2,RawAdditionIteration.step⟩ (by simp [items])
 obtain ⟨iteratorTag,hiterator⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨2,RawAdditionIteration.iterator⟩ (by simp [items])
 obtain ⟨numeralTag,hnumeral⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨1,LiteralNumeralPrefix.numeralCode⟩ (by simp [items])
 obtain ⟨prefixTag,hprefix⟩ := ReflexivityInstalled.BundleProof.bundleInstallation (items old oldA x) n p tag h
  ⟨2,RawAdditionIteration.successorPrefix⟩ (by simp [items])
 let I : RawAdditionIteration.Installation p old oldA x := {
  mpTag := mpTag
  reflexivityTag := reflexivityTag
  zeroTag := zeroTag
  addTag := addTag
  replaceTag := replaceTag
  ptag := ptag
  ctag := ctag
  atag := atag
  vtag := vtag
  ftag := ftag
  ltag := ltag
  btag := btag
  arithmeticTag := arithmeticTag
  dtag := dtag
  itag := itag
  qctag := qctag
  lengthTag := lengthTag
  rightTag := rightTag
  dropTag := dropTag
  lookupTag := lookupTag
  qtag := qtag
  oldTag := oldTag
  leftTag := leftTag
  baseTag := baseTag
  stepTag := stepTag
  iteratorTag := iteratorTag
  numeralTag := numeralTag
  prefixTag := prefixTag
  utag := utag
  hmp := hmp
  hreflexivity := hreflexivity
  hzero := hzero
  hadd := hadd
  hreplace := hreplace
  hp := hp
  hc := hc
  ha := ha
  hv := hv
  hf := hf
  hl := hl
  hb := hb
  harithmetic := harithmetic
  hd := hd
  hi := hi
  hqc := hqc
  hlength := hlength
  hright := hright
  hdrop := hdrop
  hlookup := hlookup
  hq := hq
  hold := hold
  hleft := hleft
  hbase := hbase
  hstep := hstep
  hiterator := hiterator
  hnumeral := hnumeral
  hprefix := hprefix
  hu := hu
 }
 exact ⟨I,rfl⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.InstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.InstallationProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.InstallationProof.installed
