module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TagEnvironment
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.FormulaPlug
open GorbowSyntax GorbowSubstitution GorbowFormulaSubstitution GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph
open TagPlug

theorem formulaPlug {arity inputs ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (raw : List.Vector (Term ctx) inputs) (code : Term ctx) (tag : Nat)
 (hcode : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal code (rawNumeral (Term.numeral tag))))
 {n depth : Nat} (e : Environment n depth inputs) (f : Formula (n+1)) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaValue ctag atag (appendRaw raw code) f (tagEnvironment e))
   (formulaValue ctag atag raw (substituteFormula (CurrentRecursionBaseProgram.TagSyntax.plug n tag) f) e))) := by
 cases f with
 | equal t u =>
  obtain ⟨ht⟩ := termPlug p ctag atag hc ha e raw code tag hcode t
  obtain ⟨hu⟩ := termPlug p ctag atag hc ha e raw code tag hcode u
  exact CurrentCompositionCertificate.CodecProof.binary p ctag atag ctag atag 0 hc ha hc ha _ _ _ _ ht hu
 | universalRelation t =>
  obtain ⟨ht⟩ := termPlug p ctag atag hc ha e raw code tag hcode t
  exact CurrentCompositionCertificate.CodecProof.unary p ctag ctag 1 hc hc _ _ ht
 | agent t =>
  obtain ⟨ht⟩ := termPlug p ctag atag hc ha e raw code tag hcode t
  exact CurrentCompositionCertificate.CodecProof.unary p ctag ctag 2 hc hc _ _ ht
 | knowledgeAll t =>
  obtain ⟨ht⟩ := termPlug p ctag atag hc ha e raw code tag hcode t
  exact CurrentCompositionCertificate.CodecProof.unary p ctag ctag 3 hc hc _ _ ht
 | truth t =>
  obtain ⟨ht⟩ := termPlug p ctag atag hc ha e raw code tag hcode t
  exact CurrentCompositionCertificate.CodecProof.unary p ctag ctag 5 hc hc _ _ ht
 | knowledge t u =>
  obtain ⟨ht⟩ := termPlug p ctag atag hc ha e raw code tag hcode t
  obtain ⟨hu⟩ := termPlug p ctag atag hc ha e raw code tag hcode u
  exact CurrentCompositionCertificate.CodecProof.binary p ctag atag ctag atag 4 hc ha hc ha _ _ _ _ ht hu
 | neg f =>
  obtain ⟨hf⟩ := formulaPlug p ctag atag hc ha raw code tag hcode e f
  exact CurrentCompositionCertificate.CodecProof.unary p ctag ctag 6 hc hc _ _ hf
 | imp f g =>
  obtain ⟨hf⟩ := formulaPlug p ctag atag hc ha raw code tag hcode e f
  obtain ⟨hg⟩ := formulaPlug p ctag atag hc ha raw code tag hcode e g
  exact CurrentCompositionCertificate.CodecProof.binary p ctag atag ctag atag 7 hc ha hc ha _ _ _ _ hf hg
 | conj f g =>
  obtain ⟨hf⟩ := formulaPlug p ctag atag hc ha raw code tag hcode e f
  obtain ⟨hg⟩ := formulaPlug p ctag atag hc ha raw code tag hcode e g
  exact CurrentCompositionCertificate.CodecProof.binary p ctag atag ctag atag 8 hc ha hc ha _ _ _ _ hf hg
 | disj f g =>
  obtain ⟨hf⟩ := formulaPlug p ctag atag hc ha raw code tag hcode e f
  obtain ⟨hg⟩ := formulaPlug p ctag atag hc ha raw code tag hcode e g
  exact CurrentCompositionCertificate.CodecProof.binary p ctag atag ctag atag 9 hc ha hc ha _ _ _ _ hf hg
 | all f =>
  obtain ⟨hf⟩ := formulaPlug p ctag atag hc ha raw code tag hcode (liftEnvironment e) f
  have hu := CurrentCompositionCertificate.CodecProof.unary p ctag ctag 10 hc hc _ _ hf
  simpa only [formulaValue,substituteFormula,TagEnvironment.lift,CurrentRecursionBaseProgram.TagSyntax.plug] using hu
 | ex f =>
  obtain ⟨hf⟩ := formulaPlug p ctag atag hc ha raw code tag hcode (liftEnvironment e) f
  have hu := CurrentCompositionCertificate.CodecProof.unary p ctag ctag 11 hc hc _ _ hf
  simpa only [formulaValue,substituteFormula,TagEnvironment.lift,CurrentRecursionBaseProgram.TagSyntax.plug] using hu
termination_by sizeOf f
decreasing_by
 all_goals
  simp_wf
  rename_i hconstructor
  have he := eq_of_heq hconstructor
  rw [he]
  simp <;> omega

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.FormulaPlug
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.FormulaPlug
