module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.EncodingProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open GorbowFormulaSubstitution FixedFormulaSubstitution
open FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof
theorem liftEncode (n : Nat) (t : Term 0) :
 GorbowTermPrefixCode.encode (GorbowClosedEquality.liftClosedTerm n t) = GorbowTermPrefixCode.encode t := by
 induction t with
 | var i => exact Fin.elim0 i
 | zero => rfl
 | succ t ih => simp only [GorbowClosedEquality.liftClosedTerm,GorbowSubstitution.substitute,GorbowTermPrefixCode.encode] at ih ⊢; rw [ih]
 | add t u iht ihu => simp only [GorbowClosedEquality.liftClosedTerm,GorbowSubstitution.substitute,GorbowTermPrefixCode.encode] at iht ihu ⊢; rw [iht,ihu]
 | mul t u iht ihu => simp only [GorbowClosedEquality.liftClosedTerm,GorbowSubstitution.substitute,GorbowTermPrefixCode.encode] at iht ihu ⊢; rw [iht,ihu]
 | universalFunction t ih => simp only [GorbowClosedEquality.liftClosedTerm,GorbowSubstitution.substitute,GorbowTermPrefixCode.encode] at ih ⊢; rw [ih]
theorem equal {arity depth ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (a b : Term ctx) (t u : Term depth)
 (ht : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode t)))))
 (hu : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode u))))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (equalValue ctag atag a b) (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.equal t u)))))) := by
 exact binary p ctag atag hc ha 0 a b (GorbowTermPrefixCode.encode t) (GorbowTermPrefixCode.encode u) ht hu
theorem imp {arity depth ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (a b : Term ctx) (f g : Formula depth)
 (hf : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal a (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f)))))
 (hg : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal b (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode g))))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (impValue ctag atag a b) (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.imp f g)))))) := by
 exact binary p ctag atag hc ha 7 a b (GorbowFormulaPrefixCode.encode f) (GorbowFormulaPrefixCode.encode g) hf hg
theorem bound {arity ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (f : Term 1) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue ctag atag boundEnvironment (nil : List.Vector (Term ctx) 0) f)
   (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode f))))) := by
 exact FullFormulaInstantiationValidity.FixedTemplateEncodingProof.boundTermEncoding 1 f arity p ctag atag hc ha ctx
theorem assignmentSpecialized (t : Term 0) :
 assignment (UniformRuntimeEnvironmentAgreement.specialize boundEnvironment) (fun _ : Fin 1 => t) =
 Fin.cases t Fin.elim0 := by
 funext i
 cases i using Fin.cases with
 | zero =>
  change renameTerm (Fin.elim0 : Fin 0 → Fin 0) t = t
  exact congrFun (PrescribedRuntimeSpecialization.TraceSupportProof.assignmentRuntime (fun _ : Fin 1 => t)) 0
 | succ j => exact Fin.elim0 j
theorem specialized {arity ctx : Nat} (p : Program arity) (ctag atag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
 (f : Term 1) (t : Term 0) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (specializedValue ctag atag boundEnvironment f nil (rawNumeral (ctx := ctx) t))
   (rawNumeral (GorbowClosedEquality.instantiateTerm f t)))) := by
 have hraw : PrescribedRuntimeSpecialization.numeralInputs (ctx := ctx) (fun _ : Fin 1 => t) =
  rawNumeral t ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  cases i using Fin.cases with
  | zero => rfl
  | succ j => exact Fin.elim0 j
 obtain ⟨h⟩ := PrescribedRuntimeSpecialization.EncodingProof.term p ctag atag hc ha
  (UniformRuntimeEnvironmentAgreement.specialize boundEnvironment) f (fun _ : Fin 1 => t) (ctx := ctx)
 rw [assignmentSpecialized,hraw] at h
 exact ⟨h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.EncodingProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.EncodingProof
