module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.SymbolicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.TemplateTraceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open PrescribedRuntimeCallCongruence FixedFormulaSubstitution GorbowSubstitution GorbowPRDefiningEquations

theorem term {arity n depth inputs ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (e : Environment n depth inputs) (raw : List.Vector (Term ctx) inputs) (sigma : Fin n → Term depth)
 (hs : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue ctag atag e raw (.var i)) (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (sigma i)))))))
 (f : Term n) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue ctag atag e raw f) (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (substitute sigma f)))))) := by
 induction f with
 | var i => exact hs i
 | zero => exact ⟨.logical (.reflexive _)⟩
 | succ f ih =>
  obtain ⟨ih⟩ := ih
  exact FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof.unary p ctag hc 2 _ _ ih
 | add f g hf hg =>
  obtain ⟨hf⟩ := hf
  obtain ⟨hg⟩ := hg
  exact FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof.binary p ctag atag hc ha 3 _ _ _ _ hf hg
 | mul f g hf hg =>
  obtain ⟨hf⟩ := hf
  obtain ⟨hg⟩ := hg
  exact FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof.binary p ctag atag hc ha 4 _ _ _ _ hf hg
 | universalFunction f ih =>
  obtain ⟨ih⟩ := ih
  exact FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof.unary p ctag hc 5 _ _ ih

def assignment {m : Nat} (counter : Nat) (inputs : List.Vector Nat m) : Fin (m+2) → Term 1 :=
 Fin.cases (.var 0) (Fin.cases (Term.numeral counter) (fun i => GorbowClosedEquality.liftClosedTerm 1 (Term.numeral (inputs.get i))))
theorem assigned {m : Nat} (tag counter : Nat) (inputs : List.Vector Nat m) :
 substitute (assignment counter inputs) (stepTemplate m tag) = closedStepFunction tag counter inputs := by
 rw [stepTemplate,GorbowPRCallCongruence.Proof.callSubstitution]
 congr 1
 apply List.Vector.ext
 intro i
 cases i using Fin.cases with
 | zero => rfl
 | succ i => cases i using Fin.cases with
   | zero => rfl
   | succ i => rfl

theorem openStep {arity m ctx : Nat} (p : Program arity) (J : Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hn : (nodes p)[J.numeralTag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (tag counter : Nat) (inputs : List.Vector Nat m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag (stepEnvironment m)
   (LiteralNumeralPrefix.numeralCall J.numeralTag (Term.numeral counter) ::ᵥ
    CurrentCompositionCertificate.numeralValues J.numeralTag (inputs.map (Term.numeral (n := ctx)))) (stepTemplate m tag))
   (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (closedStepFunction tag counter inputs)))))) := by
 let raw := LiteralNumeralPrefix.numeralCall J.numeralTag (Term.numeral (n := ctx) counter) ::ᵥ
  CurrentCompositionCertificate.numeralValues J.numeralTag (inputs.map (Term.numeral (n := ctx)))
 have hs : ∀ i, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag (stepEnvironment m) raw (.var i))
   (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (assignment counter inputs i)))))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨.logical (.reflexive _)⟩
  | succ i => cases i using Fin.cases with
    | zero => exact ValueTraceProof.numeral p J hn counter
    | succ i =>
     have h := CurrentCompositionCertificate.NativeValuesProof.numerals (ctx := ctx) p J hn inputs i
     simpa only [termValue,stepEnvironment,assignment,Fin.cases_succ,List.Vector.get_cons_succ,
      EncodingProof.liftEncode] using h
 obtain ⟨h⟩ := term p J.ctag J.atag hc ha (stepEnvironment m) raw (assignment counter inputs) hs (stepTemplate m tag)
 rw [assigned] at h
 exact ⟨h⟩

theorem instantiateStep {m : Nat} (tag counter : Nat) (inputs : List.Vector Nat m) (value : Term 0) :
 GorbowClosedEquality.instantiateTerm (closedStepFunction tag counter inputs) value =
 call tag (Term.numeral counter ::ᵥ value ::ᵥ GorbowPRNumeralCalculation.numeralArguments inputs) := by
 let xs := GorbowPRNumeralCalculation.numeralArguments inputs
 have hl : (xs.map (GorbowClosedEquality.liftClosedTerm 1)).map (substitute (Fin.cases value Fin.elim0)) = xs := by
  apply List.Vector.ext
  intro i
  simp only [List.Vector.get_map]
  exact GorbowClosedEqualityProof.closedTransport 1 _ _
 simp only [closedStepFunction,GorbowClosedEquality.instantiateTerm,GorbowPRCallCongruence.Proof.callSubstitution,
  List.Vector.map_cons,GorbowHeaderSubstitutionProof.numerals,substitute,Fin.cases_zero,hl]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.TemplateTraceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepCertificate.TemplateTraceProof
