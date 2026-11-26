module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.Preflight
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.TermEncoding
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution GorbowSubstitution GorbowFormulaSubstitution
open FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof
theorem encoded {arity n depth inputs ctx : Nat} (p : Program arity) (c a : Nat)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[a]? = some ⟨2,HistoryAppend.append⟩)
 (e : Environment n depth inputs) (t : Term n) (raw : List.Vector (Term ctx) inputs) (u : Fin inputs → Term 0)
 (hraw : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (raw.get i) (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (u i)))))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue c a e raw t) (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (substitute (assignment e u) t)))))) := by
 induction t with
 | var i =>
  cases he : e i with
  | inl j => simp only [termValue,assignment,substitute,he]; exact ⟨.logical (.reflexive _)⟩
  | inr j =>
   simpa only [termValue,assignment,substitute,he,FixedFormulaSubstitution.NativeProof.closedEncode] using (show Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) _) from ⟨hraw j⟩)
 | zero => exact ⟨.logical (.reflexive _)⟩
 | succ t ih =>
  obtain ⟨h⟩ := ih
  exact unary p c hc 2 _ _ h
 | add t v ht hv =>
  obtain ⟨ht⟩ := ht
  obtain ⟨hv⟩ := hv
  exact binary p c a hc ha 3 _ _ _ _ ht hv
 | mul t v ht hv =>
  obtain ⟨ht⟩ := ht
  obtain ⟨hv⟩ := hv
  exact binary p c a hc ha 4 _ _ _ _ ht hv
 | universalFunction t ih =>
  obtain ⟨h⟩ := ih
  exact unary p c hc 5 _ _ h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.TermEncoding
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.TermEncoding
