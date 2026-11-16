module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CodecBridge
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CallRawCopy
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph

theorem tuple {arity ctx : Nat} (p : Program arity) (J K : PrescribedRuntimeCallCongruence.Tags)
 (hJ : CodecBridge.Nodes p J) (hK : CodecBridge.Nodes p K)
 (n : Nat) (xs ys : List.Vector (Term ctx) n)
 (hxy : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (xs.get i) (ys.get i))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (tupleValue J xs.toList) (tupleValue K ys.toList))) := by
 induction n with
 | zero =>
  have hx : xs = nil := by ext i; exact Fin.elim0 i
  have hy : ys = nil := by ext i; exact Fin.elim0 i
  subst xs; subst ys
  exact ⟨.logical (.reflexive _)⟩
 | succ n ih =>
  have hh : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal xs.head ys.head) := by
   simpa only [List.Vector.get_zero] using hxy 0
  have ht : ∀ i : Fin n, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (xs.tail.get i) (ys.tail.get i)) := by
   intro i
   rw [List.Vector.get_tail_succ,List.Vector.get_tail_succ]
   exact hxy i.succ
  obtain ⟨htail⟩ := ih xs.tail ys.tail ht
  obtain ⟨hpair⟩ := CodecBridge.pair p J K hJ hK _ _ _ _ hh htail
  have hu := CurrentCompositionCertificate.CodecProof.unary p J.ctag K.ctag 2 hJ.hc hK.hc _ _ hpair
  change Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (.equal (tupleValue J (xs.head :: xs.tail.toList)) (tupleValue K (ys.head :: ys.tail.toList)))) at hu
  simp only [← List.Vector.toList_cons,List.Vector.cons_head_tail] at hu
  exact hu

theorem call {arity ctx n : Nat} (p : Program arity) (J K : PrescribedRuntimeCallCongruence.Tags)
 (hJ : CodecBridge.Nodes p J) (hK : CodecBridge.Nodes p K) (tag : Term ctx)
 (xs ys : List.Vector (Term ctx) n)
 (hxy : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (xs.get i) (ys.get i))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (callValue J tag xs) (callValue K tag ys))) := by
 obtain ⟨ht⟩ := tuple p J K hJ hK n xs ys hxy
 obtain ⟨hn⟩ := CodecBridge.numeral p J K hJ hK tag
 obtain ⟨hp⟩ := CodecBridge.pair p J K hJ hK _ _ _ _ hn ht
 obtain ⟨hh⟩ := CodecBridge.pair p J K hJ hK _ _ _ _ (.logical (.reflexive (rawNumeral (Term.numeral n)))) hp
 exact CurrentCompositionCertificate.CodecProof.unary p J.ctag K.ctag 5 hJ.hc hK.hc _ _ hh
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CallRawCopy
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CallRawCopy
