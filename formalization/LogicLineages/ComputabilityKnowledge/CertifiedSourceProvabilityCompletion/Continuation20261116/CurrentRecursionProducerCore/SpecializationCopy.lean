module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.FormulaRaw
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CallTransport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.SpecializationCopy
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph

theorem finiteWitness (n : Nat) (F : Fin n → Sort u) (h : ∀ i, Nonempty (F i)) : Nonempty (∀ i, F i) := by
 induction n with
 | zero => exact ⟨fun i => Fin.elim0 i⟩
 | succ n ih =>
  obtain ⟨h0⟩ := h 0
  obtain ⟨hs⟩ := ih (fun i => F i.succ) (fun i => h i.succ)
  exact ⟨Fin.cases h0 hs⟩

theorem certificate {arity ctx : Nat} (p : Program arity) (J K : CurrentRecursionBaseProgram.Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hm : (nodes p)[J.mtag]? = some ⟨4,LiteralRawMP.constructor⟩) (hr : (nodes p)[J.r13]? = some ⟨2,UniformClosedRule13.lineConstructor⟩)
 (kc : (nodes p)[K.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ka : (nodes p)[K.atag]? = some ⟨2,HistoryAppend.append⟩)
 (km : (nodes p)[K.mtag]? = some ⟨4,LiteralRawMP.constructor⟩) (kr : (nodes p)[K.r13]? = some ⟨2,UniformClosedRule13.lineConstructor⟩)
 (n : Nat) (f : Formula n) (raw other : List.Vector (Term ctx) n)
 (hraw : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (raw.get i) (other.get i)))
 (a b : Term ctx) (hab : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a b)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (PrescribedRuntimeSpecialization.certificate J.mtag J.ctag J.atag J.r13 f raw a)
   (PrescribedRuntimeSpecialization.certificate K.mtag K.ctag K.atag K.r13 f other b))) := by
 induction n with
 | zero => exact ⟨hab⟩
 | succ n ih =>
  have htail : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (raw.tail.get i) (other.tail.get i)) := by
   intro i
   simpa only [List.Vector.get_tail_succ] using hraw i.succ
  obtain ⟨hcertTail⟩ := ih (.all f) raw.tail other.tail htail
  obtain ⟨hcF⟩ := FormulaCopy.formula p J.ctag J.atag K.ctag K.atag hc ha kc ka raw (PrescribedRuntimeSpecialization.runtimeEnvironment (n+1)) f
  obtain ⟨hrF⟩ := FormulaRaw.formula p K.ctag K.atag kc ka raw other hraw (PrescribedRuntimeSpecialization.runtimeEnvironment (n+1)) f
  have hf := Logic.trans _ _ _ hcF hrF
  obtain ⟨hcM⟩ := FormulaCopy.formula p J.ctag J.atag K.ctag K.atag hc ha kc ka raw.tail (PrescribedRuntimeSpecialization.headEnvironment n) f
  obtain ⟨hrM⟩ := FormulaRaw.formula p K.ctag K.atag kc ka raw.tail other.tail htail (PrescribedRuntimeSpecialization.headEnvironment n) f
  have hmat := Logic.trans _ _ _ hcM hrM
  have hh : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal raw.head other.head) := by
   simpa only [List.Vector.get_zero] using hraw 0
  obtain ⟨hline⟩ := CallTransport.rule13 p J.ctag J.r13 K.ctag K.r13 hc hr kc kr _ _ _ _ hmat hh
  obtain ⟨hmp⟩ := CallTransport.mp p J.mtag K.mtag hm km _ _ _ _ _ _ hf hline hcertTail
  simpa only [PrescribedRuntimeSpecialization.certificate,UniformRuntimeSpecializationStep.certificate,
   PrescribedRuntimeSpecialization.EnvironmentProof.stepValue,PrescribedRuntimeSpecialization.value]
   using (show Nonempty _ from ⟨hmp⟩)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.SpecializationCopy
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.SpecializationCopy
