module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CodecBridge
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph

structure Nodes {arity : Nat} (p : Program arity) (J : PrescribedRuntimeCallCongruence.Tags) : Prop where
 hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩
 ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩
 hn : (nodes p)[J.numeralTag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩

theorem numeral {arity ctx : Nat} (p : Program arity) (J K : PrescribedRuntimeCallCongruence.Tags)
 (hJ : Nodes p J) (hK : Nodes p K) (v : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralNumeralPrefix.numeralCall J.numeralTag v) (LiteralNumeralPrefix.numeralCall K.numeralTag v))) :=
 GorbowPRInternalCoherence.Proof.registryCoherence arity p J.numeralTag K.numeralTag 1 LiteralNumeralPrefix.numeralCode
  hJ.hn hK.hn ctx (v ::ᵥ nil)

theorem pair {arity ctx : Nat} (p : Program arity) (J K : PrescribedRuntimeCallCongruence.Tags)
 (hJ : Nodes p J) (hK : Nodes p K) (a b c d : Term ctx)
 (hac : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a c))
 (hbd : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b d)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (pairValue J a b) (pairValue K c d))) := by
 obtain ⟨hs⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 3 hJ.hc hJ.ha hK.hc hK.ha _ _ _ _ hac hbd
 obtain ⟨hm⟩ := CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 4 hJ.hc hJ.ha hK.hc hK.ha _ _ _ _ hs hs
 exact CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 3 hJ.hc hJ.ha hK.hc hK.ha _ _ _ _ hm hac

theorem tuple {arity ctx : Nat} (p : Program arity) (J K : PrescribedRuntimeCallCongruence.Tags)
 (hJ : Nodes p J) (hK : Nodes p K) (xs : List (Term ctx)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (tupleValue J (xs.map (LiteralNumeralPrefix.numeralCall J.numeralTag)))
   (tupleValue K (xs.map (LiteralNumeralPrefix.numeralCall K.numeralTag))))) := by
 induction xs with
 | nil => exact ⟨.logical (.reflexive _)⟩
 | cons a xs ih =>
  obtain ⟨ih⟩ := ih
  obtain ⟨ha⟩ := numeral p J K hJ hK a
  obtain ⟨hp⟩ := pair p J K hJ hK _ _ _ _ ha ih
  exact CurrentCompositionCertificate.CodecProof.unary p J.ctag K.ctag 2 hJ.hc hK.hc _ _ hp

theorem call {arity ctx m : Nat} (p : Program arity) (J K : PrescribedRuntimeCallCongruence.Tags)
 (hJ : Nodes p J) (hK : Nodes p K) (tag : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (callValue J tag (inputs.map (LiteralNumeralPrefix.numeralCall J.numeralTag)))
   (callValue K tag (inputs.map (LiteralNumeralPrefix.numeralCall K.numeralTag))))) := by
 obtain ⟨ht⟩ := tuple p J K hJ hK inputs.toList
 obtain ⟨hn⟩ := numeral p J K hJ hK tag
 obtain ⟨hp⟩ := pair p J K hJ hK _ _ _ _ hn ht
 obtain ⟨hh⟩ := pair p J K hJ hK _ _ _ _ (.logical (.reflexive (rawNumeral (Term.numeral m)))) hp
 obtain ⟨hu⟩ := CurrentCompositionCertificate.CodecProof.unary p J.ctag K.ctag 5 hJ.hc hK.hc _ _ hh
 simpa only [callValue,headerValue,List.Vector.toList_map] using (show Nonempty _ from ⟨hu⟩)

theorem calculation {arity ctx m : Nat} (p : Program arity) (J K : PrescribedRuntimeCallCongruence.Tags)
 (hJ : Nodes p J) (hK : Nodes p K) (tag : Nat) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (childFormula J tag inputs) (childFormula K tag inputs))) := by
 obtain ⟨hc⟩ := call p J K hJ hK (Term.numeral tag) inputs
 obtain ⟨hn⟩ := numeral p J K hJ hK (GorbowPRDefiningEquations.call tag inputs)
 exact CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag K.ctag K.atag 0 hJ.hc hJ.ha hK.hc hK.ha _ _ _ _ hc hn
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CodecBridge
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CodecBridge
