module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CodecBridge
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TermSubstitution
open GorbowSyntax GorbowSubstitution GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution

theorem substitution {arity n m d e r s ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (left : Environment n d r) (right : Environment m e s) (xs : List.Vector (Term ctx) r) (ys : List.Vector (Term ctx) s)
 (sigma : Fin n → Term m)
 (hvars : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue ctag atag left xs (.var i)) (termValue ctag atag right ys (sigma i)))))
 (t : Term n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue ctag atag left xs t) (termValue ctag atag right ys (substitute sigma t)))) := by
 induction t with
 | var i => exact hvars i
 | zero => exact ⟨.logical (.reflexive _)⟩
 | succ t ih =>
  obtain ⟨ih⟩ := ih
  exact CurrentCompositionCertificate.CodecProof.unary p ctag ctag 2 hc hc _ _ ih
 | add t u iht ihu =>
  obtain ⟨ht⟩ := iht
  obtain ⟨hu⟩ := ihu
  exact CurrentCompositionCertificate.CodecProof.binary p ctag atag ctag atag 3 hc ha hc ha _ _ _ _ ht hu
 | mul t u iht ihu =>
  obtain ⟨ht⟩ := iht
  obtain ⟨hu⟩ := ihu
  exact CurrentCompositionCertificate.CodecProof.binary p ctag atag ctag atag 4 hc ha hc ha _ _ _ _ ht hu
 | universalFunction t ih =>
  obtain ⟨ih⟩ := ih
  exact CurrentCompositionCertificate.CodecProof.unary p ctag ctag 5 hc hc _ _ ih

theorem congruence {arity n d e r s ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (left : Environment n d r) (right : Environment n e s) (xs : List.Vector (Term ctx) r) (ys : List.Vector (Term ctx) s)
 (hvars : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue ctag atag left xs (.var i)) (termValue ctag atag right ys (.var i)))))
 (t : Term n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue ctag atag left xs t) (termValue ctag atag right ys t))) := by
 induction t with
 | var i => exact hvars i
 | zero => exact ⟨.logical (.reflexive _)⟩
 | succ t ih =>
  obtain ⟨ih⟩ := ih
  exact CurrentCompositionCertificate.CodecProof.unary p ctag ctag 2 hc hc _ _ ih
 | add t u iht ihu =>
  obtain ⟨ht⟩ := iht
  obtain ⟨hu⟩ := ihu
  exact CurrentCompositionCertificate.CodecProof.binary p ctag atag ctag atag 3 hc ha hc ha _ _ _ _ ht hu
 | mul t u iht ihu =>
  obtain ⟨ht⟩ := iht
  obtain ⟨hu⟩ := ihu
  exact CurrentCompositionCertificate.CodecProof.binary p ctag atag ctag atag 4 hc ha hc ha _ _ _ _ ht hu
 | universalFunction t ih =>
  obtain ⟨ih⟩ := ih
  exact CurrentCompositionCertificate.CodecProof.unary p ctag ctag 5 hc hc _ _ ih
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TermSubstitution
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TermSubstitution
