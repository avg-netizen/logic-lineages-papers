module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.BaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.EncodingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261113 FixedFormulaSubstitution GorbowFormulaSubstitution
open FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof
theorem term {arity n depth inputs ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (e : Environment n depth inputs) (t : Term n) (sigma : Fin inputs → Term 0) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue ctag atag e (numeralInputs (ctx := ctx) sigma) t)
   (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode
    (GorbowSubstitution.substitute (assignment e sigma) t)))))) := by
 induction t with
 | var i =>
  cases he : e i with
  | inl j =>
   simp only [termValue,assignment,he,GorbowSubstitution.substitute]
   exact ⟨.logical (.reflexive _)⟩
  | inr j =>
   simp only [termValue,assignment,he,GorbowSubstitution.substitute,numeralInputs,List.Vector.get_ofFn,
    FixedFormulaSubstitution.NativeProof.closedEncode]
   exact ⟨.logical (.reflexive _)⟩
 | zero => exact ⟨.logical (.reflexive _)⟩
 | succ t ih =>
  obtain ⟨ht⟩ := ih
  exact unary p ctag hc 2 _ (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (assignment e sigma) t)) ht
 | add t u iht ihu =>
  obtain ⟨ht⟩ := iht
  obtain ⟨hu⟩ := ihu
  exact binary p ctag atag hc ha 3 _ _
   (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (assignment e sigma) t))
   (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (assignment e sigma) u)) ht hu
 | mul t u iht ihu =>
  obtain ⟨ht⟩ := iht
  obtain ⟨hu⟩ := ihu
  exact binary p ctag atag hc ha 4 _ _
   (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (assignment e sigma) t))
   (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (assignment e sigma) u)) ht hu
 | universalFunction t ih =>
  obtain ⟨ht⟩ := ih
  exact unary p ctag hc 5 _ (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (assignment e sigma) t)) ht
theorem formula {arity n depth inputs ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (e : Environment n depth inputs) (f : Formula n) (sigma : Fin inputs → Term 0) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaValue ctag atag (numeralInputs (ctx := ctx) sigma) f e)
   (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode
    (substituteFormula (assignment e sigma) f)))))) := by
 induction f generalizing depth with
 | equal t u =>
  obtain ⟨ht⟩ := term p ctag atag hc ha e t sigma
  obtain ⟨hu⟩ := term p ctag atag hc ha e u sigma
  exact binary p ctag atag hc ha 0 _ _
   (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (assignment e sigma) t))
   (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (assignment e sigma) u)) ht hu
 | universalRelation t =>
  obtain ⟨ht⟩ := term p ctag atag hc ha e t sigma
  exact unary p ctag hc 1 _ (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (assignment e sigma) t)) ht
 | agent t =>
  obtain ⟨ht⟩ := term p ctag atag hc ha e t sigma
  exact unary p ctag hc 2 _ (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (assignment e sigma) t)) ht
 | knowledgeAll t =>
  obtain ⟨ht⟩ := term p ctag atag hc ha e t sigma
  exact unary p ctag hc 3 _ (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (assignment e sigma) t)) ht
 | knowledge t u =>
  obtain ⟨ht⟩ := term p ctag atag hc ha e t sigma
  obtain ⟨hu⟩ := term p ctag atag hc ha e u sigma
  exact binary p ctag atag hc ha 4 _ _
   (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (assignment e sigma) t))
   (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (assignment e sigma) u)) ht hu
 | truth t =>
  obtain ⟨ht⟩ := term p ctag atag hc ha e t sigma
  exact unary p ctag hc 5 _ (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (assignment e sigma) t)) ht
 | neg f ih =>
  obtain ⟨hf⟩ := ih e
  exact unary p ctag hc 6 _ (GorbowFormulaPrefixCode.encode (substituteFormula (assignment e sigma) f)) hf
 | imp f g ihf ihg =>
  obtain ⟨hf⟩ := ihf e
  obtain ⟨hg⟩ := ihg e
  exact binary p ctag atag hc ha 7 _ _
   (GorbowFormulaPrefixCode.encode (substituteFormula (assignment e sigma) f))
   (GorbowFormulaPrefixCode.encode (substituteFormula (assignment e sigma) g)) hf hg
 | conj f g ihf ihg =>
  obtain ⟨hf⟩ := ihf e
  obtain ⟨hg⟩ := ihg e
  exact binary p ctag atag hc ha 8 _ _
   (GorbowFormulaPrefixCode.encode (substituteFormula (assignment e sigma) f))
   (GorbowFormulaPrefixCode.encode (substituteFormula (assignment e sigma) g)) hf hg
 | disj f g ihf ihg =>
  obtain ⟨hf⟩ := ihf e
  obtain ⟨hg⟩ := ihg e
  exact binary p ctag atag hc ha 9 _ _
   (GorbowFormulaPrefixCode.encode (substituteFormula (assignment e sigma) f))
   (GorbowFormulaPrefixCode.encode (substituteFormula (assignment e sigma) g)) hf hg
 | all f ih =>
  obtain ⟨hf⟩ := ih (liftEnvironment e)
  have h := unary p ctag hc 10 _
   (GorbowFormulaPrefixCode.encode (substituteFormula (assignment (liftEnvironment e) sigma) f)) hf
  simpa only [formulaValue,substituteFormula,GorbowFormulaPrefixCode.encode,
   FixedFormulaSubstitution.NativeProof.assignmentLift] using h
 | ex f ih =>
  obtain ⟨hf⟩ := ih (liftEnvironment e)
  have h := unary p ctag hc 11 _
   (GorbowFormulaPrefixCode.encode (substituteFormula (assignment (liftEnvironment e) sigma) f)) hf
  simpa only [formulaValue,substituteFormula,GorbowFormulaPrefixCode.encode,
   FixedFormulaSubstitution.NativeProof.assignmentLift] using h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.EncodingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.EncodingProof
