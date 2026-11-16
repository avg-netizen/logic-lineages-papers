module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.CodecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.TermCopiesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution
theorem term {arity n depth inputs ctx : Nat} (p : Program arity) (c a d b : Nat)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[a]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[d]? = some ⟨2,HistoryCodec.cons⟩)
 (hb : (nodes p)[b]? = some ⟨2,HistoryAppend.append⟩)
 (e : Environment n depth inputs) (raw : List.Vector (Term ctx) inputs) (t : Term n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue c a e raw t) (termValue d b e raw t))) := by
 induction t with
 | var i => exact ⟨.logical (.reflexive _)⟩
 | zero => exact ⟨.logical (.reflexive _)⟩
 | succ t ih =>
  obtain ⟨ih⟩ := ih
  exact CodecProof.unary p c d 2 hc hd _ _ ih
 | add t u iht ihu =>
  obtain ⟨ht⟩ := iht
  obtain ⟨hu⟩ := ihu
  exact CodecProof.binary p c a d b 3 hc ha hd hb _ _ _ _ ht hu
 | mul t u iht ihu =>
  obtain ⟨ht⟩ := iht
  obtain ⟨hu⟩ := ihu
  exact CodecProof.binary p c a d b 4 hc ha hd hb _ _ _ _ ht hu
 | universalFunction t ih =>
  obtain ⟨ih⟩ := ih
  exact CodecProof.unary p c d 5 hc hd _ _ ih
theorem equalFormula {arity n depth inputs ctx : Nat} (p : Program arity) (c a d b : Nat)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[a]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[d]? = some ⟨2,HistoryCodec.cons⟩)
 (hb : (nodes p)[b]? = some ⟨2,HistoryAppend.append⟩)
 (e : Environment n depth inputs) (raw : List.Vector (Term ctx) inputs) (t u : Term n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaValue c a raw (.equal t u) e) (formulaValue d b raw (.equal t u) e))) := by
 obtain ⟨ht⟩ := term p c a d b hc ha hd hb e raw t
 obtain ⟨hu⟩ := term p c a d b hc ha hd hb e raw u
 exact CodecProof.binary p c a d b 0 hc ha hd hb _ _ _ _ ht hu
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.TermCopiesProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.TermCopiesProof
