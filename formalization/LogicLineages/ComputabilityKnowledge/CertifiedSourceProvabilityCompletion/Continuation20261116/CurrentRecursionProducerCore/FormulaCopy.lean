module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CodecBridge
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.FormulaCopy
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution

theorem formula {arity inputs ctx : Nat} (p : Program arity) (c a d b : Nat)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[a]? = some ⟨2,HistoryAppend.append⟩)
 (hd : (nodes p)[d]? = some ⟨2,HistoryCodec.cons⟩) (hb : (nodes p)[b]? = some ⟨2,HistoryAppend.append⟩)
 (raw : List.Vector (Term ctx) inputs) {n depth : Nat} (e : Environment n depth inputs) (f : Formula n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaValue c a raw f e) (formulaValue d b raw f e))) := by
 cases f with
 | equal t u =>
  obtain ⟨ht⟩ := CurrentCompositionCertificate.TermCopiesProof.term p c a d b hc ha hd hb e raw t
  obtain ⟨hu⟩ := CurrentCompositionCertificate.TermCopiesProof.term p c a d b hc ha hd hb e raw u
  exact CurrentCompositionCertificate.CodecProof.binary p c a d b 0 hc ha hd hb _ _ _ _ ht hu
 | universalRelation t =>
  obtain ⟨ht⟩ := CurrentCompositionCertificate.TermCopiesProof.term p c a d b hc ha hd hb e raw t
  exact CurrentCompositionCertificate.CodecProof.unary p c d 1 hc hd _ _ ht
 | agent t =>
  obtain ⟨ht⟩ := CurrentCompositionCertificate.TermCopiesProof.term p c a d b hc ha hd hb e raw t
  exact CurrentCompositionCertificate.CodecProof.unary p c d 2 hc hd _ _ ht
 | knowledgeAll t =>
  obtain ⟨ht⟩ := CurrentCompositionCertificate.TermCopiesProof.term p c a d b hc ha hd hb e raw t
  exact CurrentCompositionCertificate.CodecProof.unary p c d 3 hc hd _ _ ht
 | truth t =>
  obtain ⟨ht⟩ := CurrentCompositionCertificate.TermCopiesProof.term p c a d b hc ha hd hb e raw t
  exact CurrentCompositionCertificate.CodecProof.unary p c d 5 hc hd _ _ ht
 | knowledge t u =>
  obtain ⟨ht⟩ := CurrentCompositionCertificate.TermCopiesProof.term p c a d b hc ha hd hb e raw t
  obtain ⟨hu⟩ := CurrentCompositionCertificate.TermCopiesProof.term p c a d b hc ha hd hb e raw u
  exact CurrentCompositionCertificate.CodecProof.binary p c a d b 4 hc ha hd hb _ _ _ _ ht hu
 | neg f =>
  obtain ⟨hf⟩ := formula p c a d b hc ha hd hb raw e f
  exact CurrentCompositionCertificate.CodecProof.unary p c d 6 hc hd _ _ hf
 | imp f g =>
  obtain ⟨hf⟩ := formula p c a d b hc ha hd hb raw e f
  obtain ⟨hg⟩ := formula p c a d b hc ha hd hb raw e g
  exact CurrentCompositionCertificate.CodecProof.binary p c a d b 7 hc ha hd hb _ _ _ _ hf hg
 | conj f g =>
  obtain ⟨hf⟩ := formula p c a d b hc ha hd hb raw e f
  obtain ⟨hg⟩ := formula p c a d b hc ha hd hb raw e g
  exact CurrentCompositionCertificate.CodecProof.binary p c a d b 8 hc ha hd hb _ _ _ _ hf hg
 | disj f g =>
  obtain ⟨hf⟩ := formula p c a d b hc ha hd hb raw e f
  obtain ⟨hg⟩ := formula p c a d b hc ha hd hb raw e g
  exact CurrentCompositionCertificate.CodecProof.binary p c a d b 9 hc ha hd hb _ _ _ _ hf hg
 | all f =>
  obtain ⟨hf⟩ := formula p c a d b hc ha hd hb raw (liftEnvironment e) f
  exact CurrentCompositionCertificate.CodecProof.unary p c d 10 hc hd _ _ hf
 | ex f =>
  obtain ⟨hf⟩ := formula p c a d b hc ha hd hb raw (liftEnvironment e) f
  exact CurrentCompositionCertificate.CodecProof.unary p c d 11 hc hd _ _ hf
termination_by structural f
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.FormulaCopy
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.FormulaCopy
