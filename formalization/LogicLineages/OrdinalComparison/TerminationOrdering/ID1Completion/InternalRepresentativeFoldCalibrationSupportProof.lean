module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier
open NumberedQuotientApplication InternalOriginalStepGuard InternalQuotientEdgeChecker
open InternalRepresentativeFoldCalibration InternalApplicationValidityStack
open InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem rootGuardCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (hv : InternalOriginalStepGuard.Calibrated n arity symbols S Gamma validity)
    (hm : InternalStructuralEndpointGuard.MembershipCalibrated S member)
    (v : List.Vector Nat 1) :
    evaluate (rootGuard validity member) v =
      sourceValidityValue n arity symbols S Gamma (v.get 0) :=
  (InternalApplicationValidityCalibrationProof.actualOriginalRecursiveValidityCalibration
    n arity symbols S Gamma validity member hv hm).1 v

theorem leafCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (old : InternalQuotientEdgeChecker.Data)
    (hv : InternalOriginalStepGuard.Calibrated n arity symbols S Gamma validity)
    (hm : InternalStructuralEndpointGuard.MembershipCalibrated S member)
    (ho : InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table old)
    (v : List.Vector Nat 1) :
    evaluate (InternalRepresentativeFoldCalibration.leaf validity member old) v =
      targetRepresentativeValue n arity symbols S Gamma (v.get 0) :=
  (InternalRepresentativeTagEvaluationProof.actualOriginalRepresentativeWrapperCalibration
    n arity symbols S Gamma table (recursiveData validity member) old
    (InternalApplicationValidityCalibrationProof.actualOriginalRecursiveValidityCalibration
      n arity symbols S Gamma validity member hv hm) ho).2.2 v

theorem targetOnPacked (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (q : Packed (Fin n) arity Gamma) :
    targetRepresentativeValue n arity symbols S Gamma (packedNumber q) =
      representativeCode symbols S q := by
  simp [targetRepresentativeValue,
    NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma q]

/-- This is only the literal combine evaluation. The explicit codomain
repacking remains visible; no off-domain representative equality is claimed. -/
theorem combineEvaluation (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (old : InternalQuotientEdgeChecker.Data)
    (ho : InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table old)
    (v : List.Vector Nat 4) :
    evaluate (combine old) v = Nat.pair (v.get 1)
      (Nat.unpair (targetRepresentativeValue n arity symbols S Gamma
        (ApplicationCertificateLift.applicationValue v))).2 := by
  rw [combine, pairOfEvaluation, rightOfEvaluation]
  change Nat.pair (v.get 1) (Nat.unpair (evaluate old.targetRepresentative
    (List.Vector.ofFn fun _ : Fin 1 =>
      evaluate InternalApplicationCertificateConstructors.application v))).2 = _
  rw [ho.2.2]
  change Nat.pair (v.get 1) (Nat.unpair (targetRepresentativeValue n arity symbols S Gamma
    (evaluate InternalApplicationCertificateConstructors.application v))).2 = _
  rw [applicationEvaluation]

/-- Original decoded representatives and original application congruence
justify combine only on the genuine typed universe children. -/
theorem typedApplicationCombine (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (hc : SubtypeClosed (fun tau => tau ∈ S))
    (Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (old : InternalQuotientEdgeChecker.Data)
    (ho : InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table old)
    (sigma tau : Ty) (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma)
    (hf : InUniverse symbols S f) (ha : InUniverse symbols S a) :
    evaluate (combine old) (List.Vector.ofFn ![typeNumber sigma,typeNumber tau,
      representativeCode symbols S ⟨.arrow sigma tau,f⟩,
      representativeCode symbols S ⟨sigma,a⟩]) =
    representativeCode symbols S (applicationPacked f a) := by
  obtain ⟨g,hg,hdg,hreg⟩ :=
    NumberedNumericApplicationSupportProof.decodedRepresentative n arity symbols S hc
      Gamma (.arrow sigma tau) f hf
  obtain ⟨b,hb,hdb,hreb⟩ :=
    NumberedNumericApplicationSupportProof.decodedRepresentative n arity symbols S hc
      Gamma sigma a ha
  have hng := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
    _ ⟨.arrow sigma tau,g⟩).mp hdg
  have hnb := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
    _ ⟨sigma,b⟩).mp hdb
  have happ : ApplicationCertificateLift.rawApplication (typeNumber sigma) (typeNumber tau)
      (representativeCode symbols S ⟨.arrow sigma tau,f⟩)
      (representativeCode symbols S ⟨sigma,a⟩) = packedNumber (applicationPacked g b) := by
    rw [← hng.1, ← hnb.1]
    simp [ApplicationCertificateLift.rawApplication, applicationPacked, packedNumber,
      termCode, codeNumber]
  have he := NumberedQuotientApplicationProof.representativeApplicationCongruence
    n arity symbols S hc Gamma sigma tau g f b a hg hf hb ha hreg hreb
  rw [combineEvaluation n arity symbols S Gamma table old ho]
  change Nat.pair (typeNumber tau) (Nat.unpair
    (targetRepresentativeValue n arity symbols S Gamma
      (ApplicationCertificateLift.rawApplication (typeNumber sigma) (typeNumber tau)
        (representativeCode symbols S ⟨.arrow sigma tau,f⟩)
        (representativeCode symbols S ⟨sigma,a⟩)))).2 = _
  rw [happ, targetOnPacked, he]
  have ht := InternalRepresentativeTagEvaluationProof.actualOriginalRepresentativeOuterType
    n arity symbols S Gamma (applicationPacked f a)
  change (Nat.unpair (representativeCode symbols S (applicationPacked f a))).1 =
    typeNumber tau at ht
  rw [← ht]
  exact Nat.pair_unpair _

theorem applicationSelectors {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    {sigma tau : Ty} (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) :
    domainValue (packedNumber (applicationPacked f a)) = typeNumber sigma ∧
    resultTypeValue (packedNumber (applicationPacked f a)) = typeNumber tau ∧
    functionChildValue (packedNumber (applicationPacked f a)) =
      packedNumber ⟨.arrow sigma tau,f⟩ ∧
    argumentChildValue (packedNumber (applicationPacked f a)) =
      packedNumber ⟨sigma,a⟩ := by
  simp [domainValue, resultTypeValue, functionChildValue, functionValue,
    argumentChildValue, argumentValue, functionPayloadValue, argumentPayloadValue,
    bodyValue, payloadValue, applicationPacked, packedNumber, termCode, codeNumber, typeNumber]

/-- The source guard is indispensable: only its successful original universe
decode supplies the four universe premises of representative congruence. -/
theorem openedRootCombine (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (hc : SubtypeClosed (fun tau => tau ∈ S))
    (Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (old : InternalQuotientEdgeChecker.Data)
    (ho : InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table old)
    (value : Nat) (ht : tagValue value = 2)
    (hs : sourceValidityValue n arity symbols S Gamma value = 1) :
    evaluate (combine old) (List.Vector.ofFn ![domainValue value,resultTypeValue value,
      targetRepresentativeValue n arity symbols S Gamma (functionChildValue value),
      targetRepresentativeValue n arity symbols S Gamma (argumentChildValue value)]) =
    targetRepresentativeValue n arity symbols S Gamma value := by
  cases hd : decodeUniverse n arity symbols S Gamma value with
  | none => simp [sourceValidityValue, rawCarrierTest, hd] at hs
  | some q =>
    obtain ⟨hnum,hq⟩ :=
      (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma value q).mp hd
    rcases q with ⟨tau,q⟩
    rw [← hnum] at ht ⊢
    cases q with
    | app f a =>
      have hf : InUniverse symbols S f := ⟨hq.1.2.1,hq.2.1⟩
      have ha : InUniverse symbols S a := ⟨hq.1.2.2,hq.2.2⟩
      have hsel := applicationSelectors f a
      simp only [applicationPacked] at hsel
      rw [hsel.1,hsel.2.1,hsel.2.2.1,hsel.2.2.2,
        targetOnPacked,targetOnPacked,targetOnPacked]
      exact typedApplicationCombine n arity symbols S hc Gamma table old ho _ _ f a hf ha
    | _ => simp [tagValue, payloadValue, packedNumber, termCode, codeNumber] at ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationSupportProof
