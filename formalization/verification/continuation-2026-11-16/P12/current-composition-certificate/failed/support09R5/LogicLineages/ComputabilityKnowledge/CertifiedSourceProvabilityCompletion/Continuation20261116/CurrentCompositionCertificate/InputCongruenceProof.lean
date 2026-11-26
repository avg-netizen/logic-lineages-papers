module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.TraceCallProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.InputCongruenceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution
theorem term {arity n depth inputs ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (e : Environment n depth inputs) (a b : List.Vector (Term ctx) inputs)
 (h : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (a.get i) (b.get i)))) (t : Term n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue ctag atag e a t) (termValue ctag atag e b t))) := by
 induction t with
 | var i =>
  cases hi : e i with
  | inl j =>
   simp only [termValue,hi]
   exact ⟨.logical (.reflexive _)⟩
  | inr j => simpa only [termValue,hi] using h j
 | zero => exact ⟨.logical (.reflexive _)⟩
 | succ t ih =>
  obtain ⟨ih⟩ := ih
  exact CodecProof.unary p ctag ctag 2 hc hc _ _ ih
 | universalFunction t ih =>
  obtain ⟨ih⟩ := ih
  exact CodecProof.unary p ctag ctag 5 hc hc _ _ ih
 | add t u iht ihu =>
  obtain ⟨ht⟩ := iht
  obtain ⟨hu⟩ := ihu
  exact CodecProof.binary p ctag atag ctag atag 3 hc ha hc ha _ _ _ _ ht hu
 | mul t u iht ihu =>
  obtain ⟨ht⟩ := iht
  obtain ⟨hu⟩ := ihu
  exact CodecProof.binary p ctag atag ctag atag 4 hc ha hc ha _ _ _ _ ht hu
theorem formula {arity n depth inputs ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (e : Environment n depth inputs) (a b : List.Vector (Term ctx) inputs)
 (h : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (a.get i) (b.get i)))) (f : Formula n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaValue ctag atag a f e) (formulaValue ctag atag b f e))) := by
 induction f generalizing depth with
 | equal t u =>
  obtain ⟨ht⟩ := term p ctag atag hc ha e a b h t
  obtain ⟨hu⟩ := term p ctag atag hc ha e a b h u
  exact CodecProof.binary p ctag atag ctag atag 0 hc ha hc ha _ _ _ _ ht hu
 | knowledge t u =>
  obtain ⟨ht⟩ := term p ctag atag hc ha e a b h t
  obtain ⟨hu⟩ := term p ctag atag hc ha e a b h u
  exact CodecProof.binary p ctag atag ctag atag 4 hc ha hc ha _ _ _ _ ht hu
 | universalRelation t =>
  obtain ⟨ht⟩ := term p ctag atag hc ha e a b h t
  exact CodecProof.unary p ctag ctag 1 hc hc _ _ ht
 | agent t =>
  obtain ⟨ht⟩ := term p ctag atag hc ha e a b h t
  exact CodecProof.unary p ctag ctag 2 hc hc _ _ ht
 | knowledgeAll t =>
  obtain ⟨ht⟩ := term p ctag atag hc ha e a b h t
  exact CodecProof.unary p ctag ctag 3 hc hc _ _ ht
 | truth t =>
  obtain ⟨ht⟩ := term p ctag atag hc ha e a b h t
  exact CodecProof.unary p ctag ctag 5 hc hc _ _ ht
 | neg f ih =>
  obtain ⟨ih⟩ := ih e
  exact CodecProof.unary p ctag ctag 6 hc hc _ _ ih
 | imp f g ihf ihg =>
  obtain ⟨hf⟩ := ihf e
  obtain ⟨hg⟩ := ihg e
  exact CodecProof.binary p ctag atag ctag atag 7 hc ha hc ha _ _ _ _ hf hg
 | conj f g ihf ihg =>
  obtain ⟨hf⟩ := ihf e
  obtain ⟨hg⟩ := ihg e
  exact CodecProof.binary p ctag atag ctag atag 8 hc ha hc ha _ _ _ _ hf hg
 | disj f g ihf ihg =>
  obtain ⟨hf⟩ := ihf e
  obtain ⟨hg⟩ := ihg e
  exact CodecProof.binary p ctag atag ctag atag 9 hc ha hc ha _ _ _ _ hf hg
 | all f ih =>
  obtain ⟨ih⟩ := ih (liftEnvironment e)
  exact CodecProof.unary p ctag ctag 10 hc hc _ _ ih
 | ex f ih =>
  obtain ⟨ih⟩ := ih (liftEnvironment e)
  exact CodecProof.unary p ctag ctag 11 hc hc _ _ ih
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.InputCongruenceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.InputCongruenceProof
