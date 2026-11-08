module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniversePrimrecProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardEvaluationProof
open Source NumberedNumericCarrier NumberedNumericDecoding NumberedNumericStep NumberedLeastCodeRepresentative
open InternalOriginalStepGuard InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof InternalAcceptanceCalibrationProof
open InternalEqualityTestEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

attribute [local irreducible] Primrec

 theorem actualOriginalValidityProgramsExist :
    InternalOriginalStepGuardTargets.ActualOriginalValidityProgramsExist := by
  intro n arity symbols S Gamma
  have hp : Primrec (fun v : List.Vector Nat 1 => v.get 0) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const 0)
  have hs : Primrec (fun v : List.Vector Nat 1 =>
      sourceValidityValue n arity symbols S Gamma (v.get 0)) :=
    (Primrec.dom_bool Bool.toNat).comp ((NumberedUniversePrimrecProof.rawCarrierPrimitive n arity).comp
      ((Primrec.const (symbols,S)).pair ((Primrec.const Gamma).pair hp)))
  have ht : Primrec (fun v : List.Vector Nat 1 =>
      targetValidityValue n arity Gamma (v.get 0)) :=
    (Primrec.dom_bool Bool.toNat).comp (Primrec.option_isSome.comp
      ((NumberedPackedCodecPrimrecProof.packedDecoderPrimitive n arity Gamma).comp hp))
  obtain ⟨ps,hps⟩ := Proof.allPrimitiveFunctions 1 _ hs
  obtain ⟨pt,hpt⟩ := Proof.allPrimitiveFunctions 1 _ ht
  exact ⟨⟨ps,pt⟩,hps,hpt⟩

 theorem sourceAtEvaluation (data : Data) (v : List.Vector Nat 3) :
    evaluate (sourceAt data) v = evaluate data.sourceValid (List.Vector.ofFn ![v.get 0]) := rfl

 theorem targetAtEvaluation (data : Data) (v : List.Vector Nat 3) :
    evaluate (targetAt data) v = evaluate data.targetValid (List.Vector.ofFn ![v.get 1]) := rfl

 theorem sameOuterTypesEvaluation (v : List.Vector Nat 3) :
    evaluate sameOuterTypes v =
      if (Nat.unpair (v.get 0)).1 = (Nat.unpair (v.get 1)).1 then 1 else 0 := by
  change evaluate InternalEqualityTest.equalityTest
    (List.Vector.ofFn fun i : Fin 2 =>
      evaluate ((![leftOf (.projection 0),leftOf (.projection 1)] : Fin 2 → Program 3) i) v) = _
  rw [vectorTwo,exactEqualityEvaluation]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,leftOfEvaluation,evaluate]

/-- This external statement only inspects the unchanged step decoder. -/
 theorem originalAcceptanceGuards (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (s t k : Nat) (h : numericStepTest n arity symbols S Gamma table s t k = true) :
    sourceValidityValue n arity symbols S Gamma s = 1 ∧
      targetValidityValue n arity Gamma t = 1 ∧ (Nat.unpair s).1 = (Nat.unpair t).1 := by
  cases hs : decodeUniverse n arity symbols S Gamma s with
  | none => simp only [numericStepTest,hs,Bool.false_eq_true] at h
  | some q =>
    cases ht : decodePackedNumber n arity Gamma t with
    | none => simp only [numericStepTest,hs,ht,Bool.false_eq_true] at h
    | some r =>
      cases hk : decodeStepCertificate k with
      | none => simp only [numericStepTest,hs,ht,hk,Bool.false_eq_true] at h
      | some c =>
        have he : r.1 = q.1 := by
          by_contra hn
          simp [numericStepTest,hs,ht,hk,hn] at h
        refine ⟨by simp only [sourceValidityValue,rawCarrierTest,hs,Option.isSome_some,Bool.toNat_true],
          by simp only [targetValidityValue,ht,Option.isSome_some,Bool.toNat_true],?_⟩
        have hsp : decodePackedNumber n arity Gamma s = some q := by
          exact (Option.filter_eq_some_iff.mp hs).1
        have hsq := NumberedNumericDecodingProof.packedNumericSound n arity Gamma s q hsp
        have htr := NumberedNumericDecodingProof.packedNumericSound n arity Gamma t r ht
        rw [← hsq,← htr]
        simp only [packedNumber,Nat.unpair_pair]
        exact congrArg typeNumber he.symm

 theorem actualOriginalGuardedStepCalibration :
    InternalOriginalStepGuardTargets.ActualOriginalGuardedStepCalibration := by
  intro n arity symbols S Gamma table data oldChecker hd ho v
  have hs := hd.1 (List.Vector.ofFn ![v.get 0])
  have ht := hd.2 (List.Vector.ofFn ![v.get 1])
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero] at hs ht
  rw [checker,actualConjunctionEvaluation,ho]
  cases hn : numericStepTest n arity symbols S Gamma table (v.get 0) (v.get 1) (v.get 2) with
  | false => simp only [Bool.toNat_false,Nat.zero_ne_one,and_false,ite_false]
  | true =>
    obtain ⟨hsource,htarget,he⟩ := originalAcceptanceGuards n arity symbols S Gamma table
      (v.get 0) (v.get 1) (v.get 2) hn
    have hg : evaluate (guards data) v = 1 := by
      rw [guards,actualConjunctionEvaluation,actualConjunctionEvaluation,
        sourceAtEvaluation,targetAtEvaluation,sameOuterTypesEvaluation,hs,ht,hsource,htarget]
      simp only [he,ite_true,and_self]
    simp only [hg,Bool.toNat_true,and_self,ite_true]

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardEvaluationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardEvaluationProof
