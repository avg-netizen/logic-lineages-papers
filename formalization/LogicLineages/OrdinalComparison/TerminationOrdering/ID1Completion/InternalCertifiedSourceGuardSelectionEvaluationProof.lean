module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionEvaluationProof
open Source NumberedNumericCarrier NumberedNumericDecoding NumberedLeastCodeRepresentative NumberedTypedCarrier
open InternalCertifiedSourceGuardSelection
open InternalApplicationStepPeelEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem unaryAtEvaluation {m : Nat} (p : Program 1) (i : Fin m)
    (v : List.Vector Nat m) :
    evaluate (unaryAt p i) v = evaluate p (List.Vector.ofFn ![v.get i]) := rfl

theorem fixedPointEvaluation (data : Data) (v : List.Vector Nat 2) :
    evaluate (fixedPoint data) v =
      if evaluate (normalizer data) (List.Vector.ofFn ![v.get 0]) = v.get 0 then 1 else 0 := by
  rw [fixedPoint, sameEvaluation, unaryAtEvaluation]
  rfl

theorem baseCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data)
    (h : Calibrated n arity symbols S Gamma table data) :
    InternalOriginalApplicationStep.SelectedCalibrated n arity symbols S Gamma table
      (baseData data) :=
  InternalOriginalApplicationStepEvaluationProof.selectedCalibration
    n arity symbols S Gamma table (baseData data) ⟨h.1,h.2.1,h.2.2.1.1⟩

theorem goodRunCalibration (data : Data) (value : Nat) :
    evaluate (goodRun data) (List.Vector.ofFn ![value]) = 1 :=
  InternalApplicationCertifiedResultFoldClosureCalibrationProof.actualOriginalResultFoldGoodRunCalibration
    (InternalRepresentativeFoldCalibration.rootGuard data.oldValidity data.member)
    (InternalRepresentativeFoldCalibration.leaf data.oldValidity data.member data.oldEdge)
    (InternalRepresentativeFoldCalibration.combine data.oldEdge) value

/-- The new raw-target universe check is redundant ONLY on accepted
original steps under the original subtype-closed window hypothesis. -/
theorem originalStepTargetUniverse (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (hc : SubtypeClosed (fun tau => tau ∈ S)) (s t k : Nat)
    (h : NumberedNumericStep.numericStepTest n arity symbols S Gamma table s t k = true) :
    InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma t = 1 := by
  obtain ⟨tau,q,r,hq,hr,hstep,hqn,hrn⟩ :=
    NumberedNumericStepProof.numericStepSound n arity symbols S hc Gamma table s t k h
  have hd := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma t
    (⟨tau,r⟩ : NumberedRewriteReduction.Packed (Fin n) arity Gamma)).mpr ⟨hrn,hr⟩
  simp only [InternalOriginalStepGuard.sourceValidityValue,rawCarrierTest,hd,
    Option.isSome_some,Bool.toNat_true]

theorem stepCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data)
    (hc : SubtypeClosed (fun tau => tau ∈ S))
    (h : Calibrated n arity symbols S Gamma table data) :
    InternalApplicationStepChecker.StepCalibrated n arity symbols S Gamma table
      (stepChecker data) := by
  intro v
  have hb : evaluate (baseStep data) v =
      (NumberedNumericStep.numericStepTest n arity symbols S Gamma table
        (v.get 0) (v.get 1) (v.get 2)).toNat :=
    (baseCalibration n arity symbols S Gamma table data h).2.2 v
  have hv : evaluate (validity data).sourceValid (List.Vector.ofFn ![v.get 1]) =
      InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma (v.get 1) :=
    (baseCalibration n arity symbols S Gamma table data h).1.1 (List.Vector.ofFn ![v.get 1])
  rw [stepChecker,conjunctionEvaluation,hb]
  cases hn : NumberedNumericStep.numericStepTest n arity symbols S Gamma table
      (v.get 0) (v.get 1) (v.get 2) with
  | false => simp
  | true =>
    have ht := originalStepTargetUniverse n arity symbols S Gamma table hc
      (v.get 0) (v.get 1) (v.get 2) hn
    rw [conjunctionEvaluation,conjunctionEvaluation,unaryAtEvaluation,
      unaryAtEvaluation,unaryAtEvaluation,hv,ht,goodRunCalibration,goodRunCalibration]
    simp

/-- The original typed test includes its literal canonical representative
condition. On its accepted inputs the packed-target representative is the
same raw value, without changing any target decoder on other inputs. -/
theorem originalTypedRepresentativeFixed (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (v : List.Vector Nat 2)
    (h : InternalOriginalTypedCarrier.typedValue n arity symbols S Gamma v = 1) :
    InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma
      (v.get 0) = v.get 0 := by
  obtain ⟨tau,ht,htn⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal (v.get 1)
  cases hq : decodeUniverse n arity symbols S Gamma (v.get 0) with
  | none =>
    simp only [InternalOriginalTypedCarrier.typedValue,ht,Option.any_some,
      typedCanonicalCarrierTest,hq,Option.any_none,Bool.toNat_false,Nat.zero_ne_one] at h
  | some q =>
    have hb : q.1 = tau ∧ representativeCode symbols S q = v.get 0 := by
      simpa only [InternalOriginalTypedCarrier.typedValue,ht,Option.any_some,
        typedCanonicalCarrierTest,hq,OrdinaryArithmeticQuotientProof.boolNatOne,
        decide_eq_true_eq] using h
    have hp : decodePackedNumber n arity Gamma (v.get 0) = some q :=
      (Option.filter_eq_some_iff.mp hq).1
    simp only [InternalQuotientEdgeChecker.targetRepresentativeValue,hp]
    exact hb.2

theorem typedNormalizerFixed (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : Data) (hc : SubtypeClosed (fun tau => tau ∈ S))
    (h : Calibrated n arity symbols S Gamma table data) (v : List.Vector Nat 2)
    (ht : InternalOriginalTypedCarrier.typedValue n arity symbols S Gamma v = 1) :
    evaluate (normalizer data) (List.Vector.ofFn ![v.get 0]) = v.get 0 := by
  have hn := InternalRepresentativeFoldCalibrationProof.normalizerCalibration
    n arity symbols S Gamma table data.oldValidity data.member data.oldEdge
    hc h.1 h.2.1 h.2.2.1 (List.Vector.ofFn ![v.get 0])
  exact hn.trans (originalTypedRepresentativeFixed n arity symbols S Gamma v ht)

theorem typedCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data)
    (hc : SubtypeClosed (fun tau => tau ∈ S))
    (h : Calibrated n arity symbols S Gamma table data) :
    InternalOriginalTypedCarrier.Calibrated n arity symbols S Gamma (typedChecker data) := by
  have hb : InternalOriginalTypedCarrier.Calibrated n arity symbols S Gamma (baseTyped data) :=
    InternalTypedEdgePresentationEvaluationProof.actualOriginalMembershipTypedCalibration
      n arity symbols S Gamma (validity data) data.member data.oldTyped
      (baseCalibration n arity symbols S Gamma table data h).1 h.2.1 h.2.2.2
  intro v
  have hbool : InternalOriginalTypedCarrier.typedValue n arity symbols S Gamma v = 0 ∨
      InternalOriginalTypedCarrier.typedValue n arity symbols S Gamma v = 1 := by
    unfold InternalOriginalTypedCarrier.typedValue
    cases (decodeType (v.get 1)).any (fun tau =>
      typedCanonicalCarrierTest n arity symbols S Gamma tau (v.get 0)) <;> simp
  rw [typedChecker,conjunctionEvaluation,hb]
  rcases hbool with hz | hone
  · simp [hz]
  · have hn := typedNormalizerFixed n arity symbols S Gamma table data hc h v hone
    rw [conjunctionEvaluation,unaryAtEvaluation,goodRunCalibration,fixedPointEvaluation,hn]
    simp [hone]

theorem selectedCalibration :
    InternalCertifiedSourceGuardSelectionTargets.ActualOriginalCertifiedSourceGuardCalibration := by
  intro n arity symbols S Gamma table data hc h
  have hb := baseCalibration n arity symbols S Gamma table data h
  have hf := InternalRepresentativeFoldCalibrationProof.actualOriginalRepresentativeFoldProgramCalibration
    n arity symbols S Gamma table data.oldValidity data.member data.oldEdge hc h.1 h.2.1 h.2.2.1
  have hr : InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table
      (representatives data) :=
    InternalRepresentativeTagProof.actualOriginalRepresentativeWrapperCalibration
      n arity symbols S Gamma table (validity data)
      (InternalRepresentativeFoldCalibration.foldedData data.oldValidity data.member data.oldEdge)
      hb.1 hf
  have he : InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table (edgeData data) :=
    ⟨stepCalibration n arity symbols S Gamma table data hc h,hr.2⟩
  exact ⟨hb,he,typedCalibration n arity symbols S Gamma table data hc h,
    InternalQuotientEdgeCheckerEvaluationProof.actualOriginalCheckerCalibration
      n arity symbols S Gamma table (edgeData data) he⟩

theorem calibratedDataExists (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) :
    ∃ data : Data, Calibrated n arity symbols S Gamma table data := by
  obtain ⟨data,h⟩ := InternalTypedEdgePresentationEvaluationProof.calibratedDataExists
    n arity symbols S Gamma table
  exact ⟨⟨data.validity,data.member,data.oldEdge,data.oldTyped⟩,h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionEvaluationProof
