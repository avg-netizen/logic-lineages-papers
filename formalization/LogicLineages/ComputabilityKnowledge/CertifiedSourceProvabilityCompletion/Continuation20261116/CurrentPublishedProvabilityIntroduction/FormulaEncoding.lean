module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.TermEncoding
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.FormulaEncoding
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution GorbowSubstitution GorbowFormulaSubstitution
open FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof
theorem encoded {arity inputs ctx n depth : Nat} (p : Program arity) (c a : Nat)
 (hc : (nodes p)[c]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[a]? = some ⟨2,HistoryAppend.append⟩)
 (e : Environment n depth inputs) (f : Formula n) (raw : List.Vector (Term ctx) inputs) (u : Fin inputs → Term 0)
 (hraw : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (raw.get i) (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (u i)))))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaValue c a raw f e) (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (substituteFormula (assignment e u) f)))))) := by
 induction f generalizing depth with
 | equal t v =>
  obtain ⟨ht⟩ := TermEncoding.encoded p c a hc ha e t raw u hraw
  obtain ⟨hv⟩ := TermEncoding.encoded p c a hc ha e v raw u hraw
  exact binary p c a hc ha 0 _ _ _ _ ht hv
 | knowledge t v =>
  obtain ⟨ht⟩ := TermEncoding.encoded p c a hc ha e t raw u hraw
  obtain ⟨hv⟩ := TermEncoding.encoded p c a hc ha e v raw u hraw
  exact binary p c a hc ha 4 _ _ _ _ ht hv
 | universalRelation t =>
  obtain ⟨ht⟩ := TermEncoding.encoded p c a hc ha e t raw u hraw
  exact unary p c hc 1 _ _ ht
 | agent t =>
  obtain ⟨ht⟩ := TermEncoding.encoded p c a hc ha e t raw u hraw
  exact unary p c hc 2 _ _ ht
 | knowledgeAll t =>
  obtain ⟨ht⟩ := TermEncoding.encoded p c a hc ha e t raw u hraw
  exact unary p c hc 3 _ _ ht
 | truth t =>
  obtain ⟨ht⟩ := TermEncoding.encoded p c a hc ha e t raw u hraw
  exact unary p c hc 5 _ _ ht
 | neg f ih =>
  obtain ⟨h⟩ := ih e
  exact unary p c hc 6 _ _ h
 | imp f g hf hg =>
  obtain ⟨hf⟩ := hf e
  obtain ⟨hg⟩ := hg e
  exact binary p c a hc ha 7 _ _ _ _ hf hg
 | conj f g hf hg =>
  obtain ⟨hf⟩ := hf e
  obtain ⟨hg⟩ := hg e
  exact binary p c a hc ha 8 _ _ _ _ hf hg
 | disj f g hf hg =>
  obtain ⟨hf⟩ := hf e
  obtain ⟨hg⟩ := hg e
  exact binary p c a hc ha 9 _ _ _ _ hf hg
 | all f ih =>
  obtain ⟨h⟩ := ih (liftEnvironment e)
  rw [FixedFormulaSubstitution.NativeProof.assignmentLift] at h
  exact unary p c hc 10 _ _ h
 | ex f ih =>
  obtain ⟨h⟩ := ih (liftEnvironment e)
  rw [FixedFormulaSubstitution.NativeProof.assignmentLift] at h
  exact unary p c hc 11 _ _ h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.FormulaEncoding
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.FormulaEncoding
