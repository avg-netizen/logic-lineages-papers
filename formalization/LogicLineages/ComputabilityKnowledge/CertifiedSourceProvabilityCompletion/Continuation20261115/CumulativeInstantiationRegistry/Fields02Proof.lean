module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Fields01Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawNewestMultiplicationComputation
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationComputation
theorem installed (old a : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationComputation.Installation p old a x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAdditionIteration.installed old a x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨mulZeroTag,hmulZero⟩ := h (⟨1,RawMultiplication.Zero.lineConstructor⟩ : Packed) (by simp [items])
 obtain ⟨mulSuccTag,hmulSucc⟩ := h (⟨2,RawMultiplication.Succ.lineConstructor⟩ : Packed) (by simp [items])
 obtain ⟨congruenceStepTag,hcongruenceStep⟩ := h (⟨1,RawMulNewestSuccIteration.step⟩ : Packed) (by simp [items])
 obtain ⟨congruenceIteratorTag,hcongruenceIterator⟩ := h (⟨2,RawMulNewestSuccIteration.iterator⟩ : Packed) (by simp [items])
 exact ⟨{
  toEvaluator := parent
  mulZeroTag := mulZeroTag
  hmulZero := hmulZero
  mulSuccTag := mulSuccTag
  hmulSucc := hmulSucc
  congruenceStepTag := congruenceStepTag
  hcongruenceStep := hcongruenceStep
  congruenceIteratorTag := congruenceIteratorTag
  hcongruenceIterator := hcongruenceIterator
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawNewestMultiplicationComputation
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawNewestMultiplicationComputation
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawNewestMultiplicationIteration
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration
theorem installed (old a : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestMultiplicationIteration.Installation p old a x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawNewestMultiplicationComputation.installed old a x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨numericAddTag,hnumericAdd⟩ := h (⟨2,HistoryCodec.add⟩ : Packed) (by simp [items])
 obtain ⟨mulBaseTag,hmulBase⟩ := h (⟨1,base⟩ : Packed) (by simp [items])
 obtain ⟨mulStepTag,hmulStep⟩ := h (⟨2,step⟩ : Packed) (by simp [items])
 obtain ⟨mulIteratorTag,hmulIterator⟩ := h (⟨2,iterator⟩ : Packed) (by simp [items])
 exact ⟨{
  toComputation := parent
  numericAddTag := numericAddTag
  hnumericAdd := hnumericAdd
  mulBaseTag := mulBaseTag
  hmulBase := hmulBase
  mulStepTag := mulStepTag
  hmulStep := hmulStep
  mulIteratorTag := mulIteratorTag
  hmulIterator := hmulIterator
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawNewestMultiplicationIteration
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawNewestMultiplicationIteration
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMultiplicationEvaluation
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationEvaluation
theorem installed (old a : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationEvaluation.Installation p old a x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawNewestMultiplicationIteration.installed old a x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 exact ⟨parent⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMultiplicationEvaluation
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMultiplicationEvaluation
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAddReplacements
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddReplacements
theorem installed (old a : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddReplacements.Installation p old a x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMultiplicationEvaluation.installed old a x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨addRightLineTag,haddRightLine⟩ := h (⟨3,RawAddRightReplace.lineConstructor⟩ : Packed) (by simp [items])
 obtain ⟨addRightTestTag,haddRightTest⟩ := h (⟨2,RawAddRightReplace.candidateTest⟩ : Packed) (by simp [items])
 obtain ⟨addRightSearchTag,haddRightSearch⟩ := h (⟨3,RawSuffixSearch.search RawAddRightReplace.candidateTest⟩ : Packed) (by simp [items])
 obtain ⟨addLeftLineTag,haddLeftLine⟩ := h (⟨3,RawAddLeftReplace.lineConstructor⟩ : Packed) (by simp [items])
 obtain ⟨addLeftTestTag,haddLeftTest⟩ := h (⟨2,RawAddLeftReplace.candidateTest⟩ : Packed) (by simp [items])
 obtain ⟨addLeftSearchTag,haddLeftSearch⟩ := h (⟨2,RawNumericSearch.search RawAddLeftReplace.candidateTest⟩ : Packed) (by simp [items])
 exact ⟨{
  toCurrent := parent
  addRightLineTag := addRightLineTag
  haddRightLine := haddRightLine
  addRightTestTag := addRightTestTag
  haddRightTest := haddRightTest
  addRightSearchTag := addRightSearchTag
  haddRightSearch := haddRightSearch
  addLeftLineTag := addLeftLineTag
  haddLeftLine := haddLeftLine
  addLeftTestTag := addLeftTestTag
  haddLeftTest := haddLeftTest
  addLeftSearchTag := addLeftSearchTag
  haddLeftSearch := haddLeftSearch
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAddReplacements
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAddReplacements
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAddCongruences
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddCongruences
theorem installed (old a : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAddCongruences.Installation p old a x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAddReplacements.installed old a x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 exact ⟨parent⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAddCongruences
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAddCongruences
