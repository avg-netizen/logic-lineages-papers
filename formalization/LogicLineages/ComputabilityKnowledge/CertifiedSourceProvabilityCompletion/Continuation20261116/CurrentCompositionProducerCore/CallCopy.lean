module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.TupleCopy
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.CallCopy
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph
open CurrentRecursionProducerCore

theorem certificate {arity ctx n : Nat} (p : Program arity) (J K : PrescribedRuntimeCallCongruence.Tags)
 (H : CurrentCallCongruenceProgram.Installation p J) (L : CurrentCallCongruenceProgram.Installation p K)
 (tag : Term ctx) (xs ys codes xs' ys' codes' : List.Vector (Term ctx) n)
 (hx : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (xs.get i) (xs'.get i)))
 (hy : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (ys.get i) (ys'.get i)))
 (hc : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (codes.get i) (codes'.get i))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (callCertificate J tag xs ys codes) (callCertificate K tag xs' ys' codes'))) := by
 have hJ := TupleCopy.nodes p J H
 have hK := TupleCopy.nodes p K L
 obtain ⟨ht⟩ := TupleCopy.certificate p J K H L xs ys codes xs' ys' codes' hx hy hc
 obtain ⟨hxt⟩ := CallRawCopy.tuple p J K hJ hK n xs xs' hx
 obtain ⟨hyt⟩ := CallRawCopy.tuple p J K hJ hK n ys ys' hy
 obtain ⟨htag⟩ := CodecBridge.numeral p J K hJ hK tag
 obtain ⟨href⟩ := ScalarCopy.reflexivity p J K H L _ _ htag
 obtain ⟨hp⟩ := BinaryCopy.pair p J K H L _ _ _ _ _ _ _ _ _ _ _ _ htag hxt htag hyt href ht
 obtain ⟨htx⟩ := CodecBridge.pair p J K hJ hK _ _ _ _ htag hxt
 obtain ⟨hty⟩ := CodecBridge.pair p J K hJ hK _ _ _ _ htag hyt
 have hn : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (rawNumeral (Term.numeral n) : Term ctx) (rawNumeral (Term.numeral n))) := .logical (.reflexive _)
 obtain ⟨harn⟩ := ScalarCopy.reflexivity p J K H L _ _ hn
 obtain ⟨hh⟩ := BinaryCopy.pair p J K H L _ _ _ _ _ _ _ _ _ _ _ _ hn htx hn hty harn hp
 obtain ⟨hleft⟩ := CodecBridge.pair p J K hJ hK _ _ _ _ hn htx
 obtain ⟨hright⟩ := CodecBridge.pair p J K hJ hK _ _ _ _ hn hty
 exact ScalarCopy.ordinary p J K H L boundEnvironment (.universalFunction (.var 0)) nil nil _ _ _ _ _ _
  (fun i => Fin.elim0 i) hleft hright hh

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.CallCopy
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.CallCopy
