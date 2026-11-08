module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentativePrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerEvaluationProof
open Source NumberedRewriteReduction NumberedNumericCarrier NumberedNumericDecoding
open NumberedLeastCodeRepresentative NumberedNumericStep NumberedNumericQuotientEdge
open InternalQuotientEdgeChecker InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo exactEqualityEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

attribute [local irreducible] Primrec
attribute [local irreducible] representativeCode decodeUniverse decodePackedNumber
  sourceRepresentativeValue targetRepresentativeValue numericStepTest

theorem sourceRepresentativePrimitive (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) :
    Primrec (sourceRepresentativeValue n arity symbols S Gamma) := by
  have hd : Primrec (decodeUniverse n arity symbols S Gamma) :=
    (NumberedUniversePrimrecProof.universeDecoderPrimitive n arity Gamma).comp
      ((Primrec.const (symbols,S)).pair Primrec.id)
  have hr : Primrec (fun p : Nat × Packed (Fin n) arity Gamma =>
      representativeCode symbols S p.2) :=
    (NumberedRepresentativePrimrecProof.representativePrimitive n arity Gamma).comp
      ((Primrec.const (symbols,S)).pair Primrec.snd)
  apply (Primrec.option_casesOn hd (Primrec.const 0) hr.to₂).of_eq
  intro value
  unfold sourceRepresentativeValue
  cases decodeUniverse n arity symbols S Gamma value <;> rfl

theorem targetRepresentativePrimitive (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) :
    Primrec (targetRepresentativeValue n arity symbols S Gamma) := by
  have hd : Primrec (decodePackedNumber n arity Gamma) :=
    NumberedPackedCodecPrimrecProof.packedDecoderPrimitive n arity Gamma
  have hr : Primrec (fun p : Nat × Packed (Fin n) arity Gamma =>
      representativeCode symbols S p.2) :=
    (NumberedRepresentativePrimrecProof.representativePrimitive n arity Gamma).comp
      ((Primrec.const (symbols,S)).pair Primrec.snd)
  apply (Primrec.option_casesOn hd (Primrec.const 0) hr.to₂).of_eq
  intro value
  unfold targetRepresentativeValue
  cases decodePackedNumber n arity Gamma value <;> rfl

theorem stepPrimitive (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) :
    Primrec (fun v : List.Vector Nat 3 =>
      (numericStepTest n arity symbols S Gamma table (v.get 0) (v.get 1) (v.get 2)).toNat) := by
  have getP (i : Fin 3) : Primrec (fun v : List.Vector Nat 3 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  exact (Primrec.dom_bool Bool.toNat).comp
    ((NumberedNumericStepPrimrecProof.numericStepPrimitive n arity).comp
      ((Primrec.const (symbols,S)).pair ((Primrec.const table).pair
        ((Primrec.const Gamma).pair ((getP 0).pair ((getP 1).pair (getP 2)))))))

theorem actualOriginalProgramsExist : InternalQuotientEdgeCheckerTargets.ActualOriginalProgramsExist := by
  intro n arity symbols S Gamma table
  obtain ⟨stepProgram, hs⟩ := Proof.allPrimitiveFunctions 3 _
    (stepPrimitive n arity symbols S Gamma table)
  have getP : Primrec (fun v : List.Vector Nat 1 => v.get 0) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const 0)
  obtain ⟨sourceProgram, hsource⟩ := Proof.allPrimitiveFunctions 1 _
    ((sourceRepresentativePrimitive n arity symbols S Gamma).comp getP)
  obtain ⟨targetProgram, htarget⟩ := Proof.allPrimitiveFunctions 1 _
    ((targetRepresentativePrimitive n arity symbols S Gamma).comp getP)
  exact ⟨⟨stepProgram,sourceProgram,targetProgram⟩,hs,hsource,htarget⟩

/-- A failed original source decode already forces the original step to
reject. No window-closure hypothesis is needed. -/
theorem stepSourceFailure (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (s t k : Nat)
    (h : decodeUniverse n arity symbols S Gamma s = none) :
    numericStepTest n arity symbols S Gamma table s t k = false := by
  simp only [numericStepTest,h]

/-- The target is decoded by decodePackedNumber, exactly as in numericEdgeTest. -/
theorem stepTargetFailure (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (s t k : Nat)
    (h : decodePackedNumber n arity Gamma t = none) :
    numericStepTest n arity symbols S Gamma table s t k = false := by
  cases hs : decodeUniverse n arity symbols S Gamma s <;>
    simp only [numericStepTest,hs,h]

theorem originalEdgeDecomposition (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (x y certificate : Nat) :
    numericEdgeTest n arity symbols S Gamma table x y certificate =
      (numericStepTest n arity symbols S Gamma table
        (ApplicationCertificateLiftEdge.sourceOf certificate)
        (ApplicationCertificateLiftEdge.targetOf certificate)
        (ApplicationCertificateLiftEdge.stepOf certificate) &&
      decide (sourceRepresentativeValue n arity symbols S Gamma
        (ApplicationCertificateLiftEdge.sourceOf certificate) = x ∧
        targetRepresentativeValue n arity symbols S Gamma
          (ApplicationCertificateLiftEdge.targetOf certificate) = y)) := by
  unfold ApplicationCertificateLiftEdge.sourceOf ApplicationCertificateLiftEdge.targetOf
    ApplicationCertificateLiftEdge.stepOf
  cases hs : decodeUniverse n arity symbols S Gamma (Nat.unpair certificate).1 with
  | none =>
    have hf := stepSourceFailure n arity symbols S Gamma table
      (Nat.unpair certificate).1 (Nat.unpair (Nat.unpair certificate).2).1
      (Nat.unpair (Nat.unpair certificate).2).2 hs
    simp only [numericEdgeTest,hs,hf,Bool.false_and]
  | some q =>
    cases ht : decodePackedNumber n arity Gamma (Nat.unpair (Nat.unpair certificate).2).1 with
    | none =>
      have hf := stepTargetFailure n arity symbols S Gamma table
        (Nat.unpair certificate).1 (Nat.unpair (Nat.unpair certificate).2).1
        (Nat.unpair (Nat.unpair certificate).2).2 ht
      simp only [numericEdgeTest,hs,ht,hf,Bool.false_and]
    | some r =>
      simp only [numericEdgeTest,sourceRepresentativeValue,targetRepresentativeValue,hs,ht]

theorem fieldEvaluation (selector : Program 1) (v : List.Vector Nat 3) :
    evaluate (field selector) v = evaluate selector (v.get 2 ::ᵥ List.Vector.nil) := by
  change evaluate selector (List.Vector.ofFn fun _ : Fin 1 => v.get 2) = _
  rw [vectorOne]

theorem sourceFieldEvaluation (v : List.Vector Nat 3) :
    evaluate (field source) v = ApplicationCertificateLiftEdge.sourceOf (v.get 2) := by
  rw [fieldEvaluation]
  exact (selectorsEvaluation (v.get 2 ::ᵥ List.Vector.nil)).1

theorem targetFieldEvaluation (v : List.Vector Nat 3) :
    evaluate (field target) v = ApplicationCertificateLiftEdge.targetOf (v.get 2) := by
  rw [fieldEvaluation]
  exact (selectorsEvaluation (v.get 2 ::ᵥ List.Vector.nil)).2.1

theorem stepFieldEvaluation (v : List.Vector Nat 3) :
    evaluate (field step) v = ApplicationCertificateLiftEdge.stepOf (v.get 2) := by
  rw [fieldEvaluation]
  exact (selectorsEvaluation (v.get 2 ::ᵥ List.Vector.nil)).2.2

theorem stepAtEvaluation (data : Data) (v : List.Vector Nat 3) :
    evaluate (stepAt data) v = evaluate data.stepProgram
      (List.Vector.ofFn ![ApplicationCertificateLiftEdge.sourceOf (v.get 2),
        ApplicationCertificateLiftEdge.targetOf (v.get 2),ApplicationCertificateLiftEdge.stepOf (v.get 2)]) := by
  change evaluate data.stepProgram (List.Vector.ofFn fun i : Fin 3 =>
    evaluate ((![field source,field target,field step] : Fin 3 → Program 3) i) v) = _
  congr 1
  apply List.Vector.ext
  intro i
  exact Fin.cases (sourceFieldEvaluation v)
    (Fin.cases (targetFieldEvaluation v) (Fin.cases (stepFieldEvaluation v) (fun q => Fin.elim0 q))) i

theorem representativeAtEvaluation (representative selector : Program 1) (v : List.Vector Nat 3) :
    evaluate (representativeAt representative selector) v =
      evaluate representative (evaluate (field selector) v ::ᵥ List.Vector.nil) := by
  change evaluate representative (List.Vector.ofFn fun _ : Fin 1 => evaluate (field selector) v) = _
  rw [vectorOne]

theorem representativeCheckEvaluation (representative selector : Program 1) (endpoint : Fin 3)
    (v : List.Vector Nat 3) :
    evaluate (representativeCheck representative selector endpoint) v =
      if evaluate (representativeAt representative selector) v = v.get endpoint then 1 else 0 := by
  change evaluate InternalEqualityTest.equalityTest (List.Vector.ofFn fun i : Fin 2 =>
    evaluate ((![representativeAt representative selector,.projection endpoint] : Fin 2 → Program 3) i) v) = _
  rw [vectorTwo]
  exact exactEqualityEvaluation _ _

theorem checkerEvaluation (data : Data) (v : List.Vector Nat 3) :
    evaluate (checker data) v =
      if evaluate (stepAt data) v = 1 ∧
        evaluate (representativeAt data.sourceRepresentative source) v = v.get 0 ∧
        evaluate (representativeAt data.targetRepresentative target) v = v.get 1 then 1 else 0 := by
  rw [checker,InternalAcceptanceCalibrationProof.actualConjunctionEvaluation,
    InternalAcceptanceCalibrationProof.actualConjunctionEvaluation,
    representativeCheckEvaluation,representativeCheckEvaluation]
  by_cases hs : evaluate (stepAt data) v = 1 <;>
    by_cases hsource : evaluate (representativeAt data.sourceRepresentative source) v = v.get 0 <;>
    by_cases htarget : evaluate (representativeAt data.targetRepresentative target) v = v.get 1 <;>
    simp [hs,hsource,htarget]

theorem booleanConjunction (b : Bool) (p : Prop) [Decidable p] :
    (if b.toNat = 1 ∧ p then 1 else 0) = (b && decide p).toNat := by
  cases b <;> by_cases hp : p <;> simp [hp]

theorem actualOriginalCheckerCalibration : InternalQuotientEdgeCheckerTargets.ActualOriginalCheckerCalibration := by
  intro n arity symbols S Gamma table data hc v
  rw [checkerEvaluation,stepAtEvaluation,hc.1,
    representativeAtEvaluation,representativeAtEvaluation,sourceFieldEvaluation,targetFieldEvaluation,
    hc.2.1,hc.2.2,originalEdgeDecomposition]
  simp only [List.Vector.get_ofFn,List.Vector.get_cons_zero]
  exact booleanConjunction
    (numericStepTest n arity symbols S Gamma table
      (ApplicationCertificateLiftEdge.sourceOf (v.get 2))
      (ApplicationCertificateLiftEdge.targetOf (v.get 2))
      (ApplicationCertificateLiftEdge.stepOf (v.get 2)))
    (sourceRepresentativeValue n arity symbols S Gamma
      (ApplicationCertificateLiftEdge.sourceOf (v.get 2)) = v.get 0 ∧
      targetRepresentativeValue n arity symbols S Gamma
        (ApplicationCertificateLiftEdge.targetOf (v.get 2)) = v.get 1)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerEvaluationProof
