module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Fields02Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAdditionEvaluation
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionEvaluation
theorem installed (old a : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulNewestAdditionEvaluation.Installation p old a x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAddCongruences.installed old a x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 exact ⟨parent⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAdditionEvaluation
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAdditionEvaluation
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawUnaryEvaluation
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnaryEvaluation
theorem installed (old a : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUnaryEvaluation.Installation p old a x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMulNewestAdditionEvaluation.installed old a x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 exact ⟨parent⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawUnaryEvaluation
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawUnaryEvaluation
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawAdditionProducer
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer
theorem installed (old a : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionProducer.Installation p old a x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawUnaryEvaluation.installed old a x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨producerTag,hproducer⟩ := h (⟨6,producer⟩ : Packed) (by simp [items])
 exact ⟨{
  toEvaluation := parent
  producerTag := producerTag
  hproducer := hproducer
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawAdditionProducer
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawAdditionProducer
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMultiplicationProducer
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationProducer
theorem installed (old a : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationProducer.Installation p old a x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawAdditionProducer.installed old a x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨multiplicationProducerTag,hmultiplicationProducer⟩ := h (⟨6,producer⟩ : Packed) (by simp [items])
 exact ⟨{
  toAdditionProducer := parent
  multiplicationProducerTag := multiplicationProducerTag
  hmultiplicationProducer := hmultiplicationProducer
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMultiplicationProducer
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMultiplicationProducer
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_ArithmeticTemplateEvaluation
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation
theorem installed (old a : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ArithmeticTemplateEvaluation.Installation p old a x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawMultiplicationProducer.installed old a x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨successorProducerTag,hsuccessorProducer⟩ := h (⟨3,RawSuccessorProducer.producer⟩ : Packed) (by simp [items])
 exact ⟨{
  toProducers := parent
  successorProducerTag := successorProducerTag
  hsuccessorProducer := hsuccessorProducer
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_ArithmeticTemplateEvaluation
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_ArithmeticTemplateEvaluation
