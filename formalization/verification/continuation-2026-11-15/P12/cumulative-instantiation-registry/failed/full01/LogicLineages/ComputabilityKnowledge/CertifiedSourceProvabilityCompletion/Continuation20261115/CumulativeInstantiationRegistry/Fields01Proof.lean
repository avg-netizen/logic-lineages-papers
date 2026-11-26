module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Fields00Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawRetainedMulRightCongruence
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedMulRightCongruence
theorem installed (old a : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedMulRightCongruence.Installation p old a x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulLeftCongruence.installed old a x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨rightLineTag,hrightLine⟩ := h (⟨3,RawMulRightReplace.lineConstructor⟩ : Packed) (by simp [items])
 obtain ⟨rightTestTag,hrightTest⟩ := h (⟨2,RawMulRightReplace.candidateTest⟩ : Packed) (by simp [items])
 obtain ⟨rightSearchTag,hrightSearch⟩ := h (⟨3,RawSuffixSearch.search RawMulRightReplace.candidateTest⟩ : Packed) (by simp [items])
 exact ⟨{
  toNewest := parent
  rightLineTag := rightLineTag
  hrightLine := hrightLine
  rightTestTag := rightTestTag
  hrightTest := hrightTest
  rightSearchTag := rightSearchTag
  hrightSearch := hrightSearch
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawRetainedMulRightCongruence
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawRetainedMulRightCongruence
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestTransitivity
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestTransitivity
theorem installed (old a : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestTransitivity.Installation p old a x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawRetainedMulRightCongruence.installed old a x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨equalityLineTag,hequalityLine⟩ := h (⟨3,RawRightReplace.lineConstructor⟩ : Packed) (by simp [items])
 exact ⟨{
  toCongruences := parent
  equalityLineTag := equalityLineTag
  hequalityLine := hequalityLine
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestTransitivity
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestTransitivity
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestSuccCongruence
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccCongruence
theorem installed (old a : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestSuccCongruence.Installation p old a x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestTransitivity.installed old a x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨replaceTag,hreplace⟩ := h (⟨2,RawSuccReplace.lineConstructor⟩ : Packed) (by simp [items])
 exact ⟨{
  toNewestEquality := parent
  replaceTag := replaceTag
  hreplace := hreplace
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestSuccCongruence
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestSuccCongruence
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAddition
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddition
theorem installed (old a : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddition.Installation p old a x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestSuccCongruence.installed old (arithmetic a) x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨zeroTag,hzero⟩ := h (⟨1,RawAddZero.lineConstructor⟩ : Packed) (by simp [items])
 obtain ⟨addTag,hadd⟩ := h (⟨2,RawAddSucc.lineConstructor⟩ : Packed) (by simp [items])
 obtain ⟨oldArithmeticTag,holdArithmetic⟩ := h (⟨1,RawCumulativeArithmetic.arithmetic a⟩ : Packed) (by simp [items])
 obtain ⟨arithmeticTag,harithmetic⟩ := h (⟨1,arithmetic a⟩ : Packed) (by simp [items])
 exact ⟨{
  toCongruence := parent
  zeroTag := zeroTag
  hzero := hzero
  addTag := addTag
  hadd := hadd
  oldArithmeticTag := oldArithmeticTag
  holdArithmetic := holdArithmetic
  arithmeticTag := arithmeticTag
  harithmetic := harithmetic
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAddition
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAddition
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAdditionIteration
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionIteration
theorem installed (old a : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionIteration.Installation p old a x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAddition.installed old a x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨rightTag,hright⟩ := h (⟨1,HistoryDecoder.decoder true⟩ : Packed) (by simp [items])
 obtain ⟨leftTag,hleft⟩ := h (⟨1,HistoryDecoder.decoder false⟩ : Packed) (by simp [items])
 obtain ⟨baseTag,hbase⟩ := h (⟨1,base⟩ : Packed) (by simp [items])
 obtain ⟨stepTag,hstep⟩ := h (⟨2,step⟩ : Packed) (by simp [items])
 obtain ⟨iteratorTag,hiterator⟩ := h (⟨2,iterator⟩ : Packed) (by simp [items])
 obtain ⟨numeralTag,hnumeral⟩ := h (⟨1,LiteralNumeralPrefix.numeralCode⟩ : Packed) (by simp [items])
 obtain ⟨prefixTag,hprefix⟩ := h (⟨2,successorPrefix⟩ : Packed) (by simp [items])
 exact ⟨{
  toAddition := parent
  rightTag := rightTag
  hright := hright
  leftTag := leftTag
  hleft := hleft
  baseTag := baseTag
  hbase := hbase
  stepTag := stepTag
  hstep := hstep
  iteratorTag := iteratorTag
  hiterator := hiterator
  numeralTag := numeralTag
  hnumeral := hnumeral
  prefixTag := prefixTag
  hprefix := hprefix
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAdditionIteration
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAdditionIteration
