module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawNumericSearch
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch
theorem installed (test : Program 2) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items test, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch.Installation p test) := by
 obtain ⟨testTag,ht⟩ := h (⟨2,test⟩ : Packed) (by simp [items])
 obtain ⟨searchTag,hs⟩ := h (⟨2,search test⟩ : Packed) (by simp [items])
 exact ⟨{
  testTag := testTag
  ht := ht
  searchTag := searchTag
  hs := hs
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawNumericSearch
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawNumericSearch
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulLeftAcceptance
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftAcceptance
theorem installed (old : Program 1) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftAcceptance.Installation p old) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawNumericSearch.installed RawMulLeftReplace.candidateTest p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨qtag,hq⟩ := h (⟨3,RawMulLeftReplace.lineConstructor⟩ : Packed) (by simp [items])
 obtain ⟨logicalTag,hlogical⟩ := h (⟨1,RawMulLeftReplace.logicalLeaf old⟩ : Packed) (by simp [items])
 obtain ⟨pairTag,hp⟩ := h (⟨2,HistoryCodec.pair⟩ : Packed) (by simp [items])
 obtain ⟨consTag,hc⟩ := h (⟨2,HistoryCodec.cons⟩ : Packed) (by simp [items])
 obtain ⟨appendTag,ha⟩ := h (⟨2,HistoryAppend.append⟩ : Packed) (by simp [items])
 obtain ⟨lengthTag,hlength⟩ := h (⟨1,HistoryLengthOffset.lengthProgram⟩ : Packed) (by simp [items])
 obtain ⟨dropTag,hdrop⟩ := h (⟨2,HistoryLookup.drop⟩ : Packed) (by simp [items])
 obtain ⟨validatorTag,hv⟩ := h (⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ : Packed) (by simp [items])
 exact ⟨{
  toSearch := parent
  qtag := qtag
  hq := hq
  logicalTag := logicalTag
  hlogical := hlogical
  pairTag := pairTag
  hp := hp
  consTag := consTag
  hc := hc
  appendTag := appendTag
  ha := ha
  lengthTag := lengthTag
  hlength := hlength
  dropTag := dropTag
  hdrop := hdrop
  validatorTag := validatorTag
  hv := hv
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulLeftAcceptance
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulLeftAcceptance
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulLeftDispatcher
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftDispatcher
theorem installed (old arithmetic : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old arithmetic x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftDispatcher.Installation p old arithmetic x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulLeftAcceptance.installed old p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨ftag,hf⟩ := h (⟨2,LiteralSyntaxValidator.formulaValidator⟩ : Packed) (by simp [items])
 obtain ⟨ltag,hlineValidator⟩ := h (⟨1,LiteralSyntaxValidator.lineValidator⟩ : Packed) (by simp [items])
 obtain ⟨dtag,hdispatcher⟩ := h (⟨4,dispatcher old arithmetic x⟩ : Packed) (by simp [items])
 exact ⟨{
  toAcceptance := parent
  ftag := ftag
  hf := hf
  ltag := ltag
  hlineValidator := hlineValidator
  dtag := dtag
  hdispatcher := hdispatcher
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulLeftDispatcher
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulLeftDispatcher
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulLeftCertificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftCertificate
theorem installed (old arithmetic : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old arithmetic x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftCertificate.Installation p old arithmetic x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulLeftDispatcher.installed old arithmetic x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨itag,hi⟩ := h (⟨4,SixSol20261112.HistoryMachine.iterator (kernel old arithmetic x)⟩ : Packed) (by simp [items])
 obtain ⟨qctag,hqc⟩ := h (⟨5,checker old arithmetic x⟩ : Packed) (by simp [items])
 obtain ⟨utag,hu⟩ := h (⟨5,verifier old arithmetic x⟩ : Packed) (by simp [items])
 exact ⟨{
  toDispatcher := parent
  itag := itag
  hi := hi
  qctag := qctag
  hqc := hqc
  utag := utag
  hu := hu
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulLeftCertificate
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulLeftCertificate
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulLeftCongruence
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftCongruence
theorem installed (old a : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulLeftCongruence.Installation p old a x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulLeftCertificate.installed (RawMulLeftCongruence.previousLogical old) a x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨addLeftTag,haddLeft⟩ := h (⟨1,RawMulRightCongruence.previousLogical old⟩ : Packed) (by simp [items])
 obtain ⟨rightReplaceTag,hrightReplace⟩ := h (⟨1,RawRightReplace.logicalLeaf (RawCumulativeLogical.logical old)⟩ : Packed) (by simp [items])
 obtain ⟨addRightTag,haddRight⟩ := h (⟨1,RawAddLeftCongruence.previousLogical old⟩ : Packed) (by simp [items])
 obtain ⟨cumulativeTag,hcumulative⟩ := h (⟨1,RawCumulativeLogical.logical old⟩ : Packed) (by simp [items])
 obtain ⟨previousTag,hprevious⟩ := h (⟨1,RawMulLeftCongruence.previousLogical old⟩ : Packed) (by simp [items])
 obtain ⟨reflexivityTag,hreflexivity⟩ := h (⟨1,RawReflexivity.lineConstructor⟩ : Packed) (by simp [items])
 obtain ⟨lookupTag,hlookup⟩ := h (⟨2,HistoryLookup.lookup⟩ : Packed) (by simp [items])
 obtain ⟨mpTag,hmp⟩ := h (⟨4,LiteralRawMP.constructor⟩ : Packed) (by simp [items])
 exact ⟨{
  toCertificate := parent
  addLeftTag := addLeftTag
  haddLeft := haddLeft
  rightReplaceTag := rightReplaceTag
  hrightReplace := hrightReplace
  addRightTag := addRightTag
  haddRight := haddRight
  cumulativeTag := cumulativeTag
  hcumulative := hcumulative
  previousTag := previousTag
  hprevious := hprevious
  reflexivityTag := reflexivityTag
  hreflexivity := hreflexivity
  lookupTag := lookupTag
  hlookup := hlookup
  mpTag := mpTag
  hmp := hmp
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulLeftCongruence
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulLeftCongruence
