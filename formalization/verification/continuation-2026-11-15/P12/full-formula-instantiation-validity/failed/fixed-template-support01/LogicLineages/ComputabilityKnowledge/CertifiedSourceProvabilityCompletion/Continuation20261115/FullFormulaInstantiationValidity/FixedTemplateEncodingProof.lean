module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTemplateEncodingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261113 FixedFormulaSubstitution FixedTemplateEncodingTargets FixedTemplateEncodingSupportProof
/-- Every original term constructor has its literal prefix numeral code. -/
theorem boundTermEncoding : InternalBoundTermEncoding := by
 intro n t arity p ctag atag hc ha ctx
 induction t with
 | var i => exact ⟨.logical (.reflexive _)⟩
 | zero => exact ⟨.logical (.reflexive _)⟩
 | succ t ih =>
  obtain ⟨ht⟩ := ih
  exact unary p ctag hc 2 _ (GorbowTermPrefixCode.encode t) ht
 | add t u iht ihu =>
  obtain ⟨ht⟩ := iht
  obtain ⟨hu⟩ := ihu
  exact binary p ctag atag hc ha 3 _ _ (GorbowTermPrefixCode.encode t) (GorbowTermPrefixCode.encode u) ht hu
 | mul t u iht ihu =>
  obtain ⟨ht⟩ := iht
  obtain ⟨hu⟩ := ihu
  exact binary p ctag atag hc ha 4 _ _ (GorbowTermPrefixCode.encode t) (GorbowTermPrefixCode.encode u) ht hu
 | universalFunction t ih =>
  obtain ⟨ht⟩ := ih
  exact unary p ctag hc 5 _ (GorbowTermPrefixCode.encode t) ht
/-- Every full formula constructor retains the original encoded template;
binder lifting is proved, not identified with a different environment. -/
theorem boundFormulaEncoding : InternalBoundFormulaEncoding := by
 intro n f arity p ctag atag hc ha ctx
 induction f with
 | equal t u =>
  obtain ⟨ht⟩ := boundTermEncoding _ t arity p ctag atag hc ha ctx
  obtain ⟨hu⟩ := boundTermEncoding _ u arity p ctag atag hc ha ctx
  exact binary p ctag atag hc ha 0 _ _ (GorbowTermPrefixCode.encode t) (GorbowTermPrefixCode.encode u) ht hu
 | universalRelation t =>
  obtain ⟨ht⟩ := boundTermEncoding _ t arity p ctag atag hc ha ctx
  exact unary p ctag hc 1 _ (GorbowTermPrefixCode.encode t) ht
 | agent t =>
  obtain ⟨ht⟩ := boundTermEncoding _ t arity p ctag atag hc ha ctx
  exact unary p ctag hc 2 _ (GorbowTermPrefixCode.encode t) ht
 | knowledgeAll t =>
  obtain ⟨ht⟩ := boundTermEncoding _ t arity p ctag atag hc ha ctx
  exact unary p ctag hc 3 _ (GorbowTermPrefixCode.encode t) ht
 | knowledge t u =>
  obtain ⟨ht⟩ := boundTermEncoding _ t arity p ctag atag hc ha ctx
  obtain ⟨hu⟩ := boundTermEncoding _ u arity p ctag atag hc ha ctx
  exact binary p ctag atag hc ha 4 _ _ (GorbowTermPrefixCode.encode t) (GorbowTermPrefixCode.encode u) ht hu
 | truth t =>
  obtain ⟨ht⟩ := boundTermEncoding _ t arity p ctag atag hc ha ctx
  exact unary p ctag hc 5 _ (GorbowTermPrefixCode.encode t) ht
 | neg f ih =>
  obtain ⟨hf⟩ := ih
  exact unary p ctag hc 6 _ (GorbowFormulaPrefixCode.encode f) hf
 | imp f g ihf ihg =>
  obtain ⟨hf⟩ := ihf
  obtain ⟨hg⟩ := ihg
  exact binary p ctag atag hc ha 7 _ _ (GorbowFormulaPrefixCode.encode f) (GorbowFormulaPrefixCode.encode g) hf hg
 | conj f g ihf ihg =>
  obtain ⟨hf⟩ := ihf
  obtain ⟨hg⟩ := ihg
  exact binary p ctag atag hc ha 8 _ _ (GorbowFormulaPrefixCode.encode f) (GorbowFormulaPrefixCode.encode g) hf hg
 | disj f g ihf ihg =>
  obtain ⟨hf⟩ := ihf
  obtain ⟨hg⟩ := ihg
  exact binary p ctag atag hc ha 9 _ _ (GorbowFormulaPrefixCode.encode f) (GorbowFormulaPrefixCode.encode g) hf hg
 | all f ih =>
  obtain ⟨hf⟩ := ih
  have h := unary p ctag hc 10 _ (GorbowFormulaPrefixCode.encode f) hf
  simpa only [FixedFormulaSubstitution.formulaValue, liftBound, GorbowFormulaPrefixCode.encode] using h
 | ex f ih =>
  obtain ⟨hf⟩ := ih
  have h := unary p ctag hc 11 _ (GorbowFormulaPrefixCode.encode f) hf
  simpa only [FixedFormulaSubstitution.formulaValue, liftBound, GorbowFormulaPrefixCode.encode] using h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTemplateEncodingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTemplateEncodingProof
