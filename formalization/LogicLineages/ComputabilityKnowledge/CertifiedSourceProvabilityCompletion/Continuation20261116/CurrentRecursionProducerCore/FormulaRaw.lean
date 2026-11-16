module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TermSubstitution
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.FormulaRaw
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution

theorem term {arity inputs ctx n depth : Nat} (p : Program arity) (c a : Nat)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[a]? = some ⟨2,HistoryAppend.append⟩)
 (raw other : List.Vector (Term ctx) inputs)
 (hraw : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (raw.get i) (other.get i)))
 (e : Environment n depth inputs) (t : Term n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue c a e raw t) (termValue c a e other t))) := by
 apply TermSubstitution.congruence p c a hc ha e e raw other ?_ t
 intro i
 simp only [termValue]
 cases e i with
 | inl j => exact ⟨.logical (.reflexive _)⟩
 | inr j => exact ⟨hraw j⟩

theorem formula {arity inputs ctx : Nat} (p : Program arity) (c a : Nat)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[a]? = some ⟨2,HistoryAppend.append⟩)
 (raw other : List.Vector (Term ctx) inputs)
 (hraw : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (raw.get i) (other.get i)))
 {n depth : Nat} (e : Environment n depth inputs) (f : Formula n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaValue c a raw f e) (formulaValue c a other f e))) := by
 cases f with
 | equal t u =>
  obtain ⟨ht⟩ := term p c a hc ha raw other hraw e t
  obtain ⟨hu⟩ := term p c a hc ha raw other hraw e u
  exact CurrentCompositionCertificate.CodecProof.binary p c a c a 0 hc ha hc ha _ _ _ _ ht hu
 | universalRelation t =>
  obtain ⟨ht⟩ := term p c a hc ha raw other hraw e t
  exact CurrentCompositionCertificate.CodecProof.unary p c c 1 hc hc _ _ ht
 | agent t =>
  obtain ⟨ht⟩ := term p c a hc ha raw other hraw e t
  exact CurrentCompositionCertificate.CodecProof.unary p c c 2 hc hc _ _ ht
 | knowledgeAll t =>
  obtain ⟨ht⟩ := term p c a hc ha raw other hraw e t
  exact CurrentCompositionCertificate.CodecProof.unary p c c 3 hc hc _ _ ht
 | truth t =>
  obtain ⟨ht⟩ := term p c a hc ha raw other hraw e t
  exact CurrentCompositionCertificate.CodecProof.unary p c c 5 hc hc _ _ ht
 | knowledge t u =>
  obtain ⟨ht⟩ := term p c a hc ha raw other hraw e t
  obtain ⟨hu⟩ := term p c a hc ha raw other hraw e u
  exact CurrentCompositionCertificate.CodecProof.binary p c a c a 4 hc ha hc ha _ _ _ _ ht hu
 | neg f =>
  obtain ⟨hf⟩ := formula p c a hc ha raw other hraw e f
  exact CurrentCompositionCertificate.CodecProof.unary p c c 6 hc hc _ _ hf
 | imp f g =>
  obtain ⟨hf⟩ := formula p c a hc ha raw other hraw e f
  obtain ⟨hg⟩ := formula p c a hc ha raw other hraw e g
  exact CurrentCompositionCertificate.CodecProof.binary p c a c a 7 hc ha hc ha _ _ _ _ hf hg
 | conj f g =>
  obtain ⟨hf⟩ := formula p c a hc ha raw other hraw e f
  obtain ⟨hg⟩ := formula p c a hc ha raw other hraw e g
  exact CurrentCompositionCertificate.CodecProof.binary p c a c a 8 hc ha hc ha _ _ _ _ hf hg
 | disj f g =>
  obtain ⟨hf⟩ := formula p c a hc ha raw other hraw e f
  obtain ⟨hg⟩ := formula p c a hc ha raw other hraw e g
  exact CurrentCompositionCertificate.CodecProof.binary p c a c a 9 hc ha hc ha _ _ _ _ hf hg
 | all f =>
  obtain ⟨hf⟩ := formula p c a hc ha raw other hraw (liftEnvironment e) f
  exact CurrentCompositionCertificate.CodecProof.unary p c c 10 hc hc _ _ hf
 | ex f =>
  obtain ⟨hf⟩ := formula p c a hc ha raw other hraw (liftEnvironment e) f
  exact CurrentCompositionCertificate.CodecProof.unary p c c 11 hc hc _ _ hf
termination_by sizeOf f
decreasing_by all_goals simp_wf <;> omega
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.FormulaRaw
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.FormulaRaw
