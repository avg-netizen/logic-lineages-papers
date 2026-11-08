module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationApplicationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier
open NumberedQuotientApplication InternalOriginalStepGuard InternalQuotientEdgeChecker
open InternalCanonicalResultFoldCalibration InternalApplicationValidityStack
open InternalCanonicalResultFoldCalibrationSupportProof
open InternalRepresentativeFoldCalibrationSupportProof (targetOnPacked applicationSelectors)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The exact NEW combine uses D after raw application. The old combine's
codomain overwrite and its calibration are not used. -/
 theorem typedApplicationCombine (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (hc : SubtypeClosed (fun tau => tau ∈ S))
    (Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalDescentSelection.Data)
    (h : InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data)
    (sigma tau : Ty) (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma)
    (hf : InUniverse symbols S f) (ha : InUniverse symbols S a) :
    evaluate (combine data) (List.Vector.ofFn ![typeNumber sigma,typeNumber tau,
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
    simp [ApplicationCertificateLift.rawApplication,applicationPacked,packedNumber,
      termCode,codeNumber]
  have he := NumberedQuotientApplicationProof.representativeApplicationCongruence
    n arity symbols S hc Gamma sigma tau g f b a hg hf hb ha hreg hreb
  rw [combineCalibration n arity symbols S Gamma table data hc h]
  change targetRepresentativeValue n arity symbols S Gamma
    (ApplicationCertificateLift.rawApplication (typeNumber sigma) (typeNumber tau)
      (representativeCode symbols S ⟨.arrow sigma tau,f⟩)
      (representativeCode symbols S ⟨sigma,a⟩)) = _
  rw [happ,targetOnPacked,he]

/-- Source-universe decoding of the original opened root supplies the typed
children needed by original representative congruence. There is no input
canonicality requirement and no claim for source-invalid applications. -/
 theorem openedRootCombine (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (hc : SubtypeClosed (fun tau => tau ∈ S))
    (Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalDescentSelection.Data)
    (h : InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data)
    (value : Nat) (ht : tagValue value = 2)
    (hs : sourceValidityValue n arity symbols S Gamma value = 1) :
    evaluate (combine data) (List.Vector.ofFn ![domainValue value,resultTypeValue value,
      targetRepresentativeValue n arity symbols S Gamma (functionChildValue value),
      targetRepresentativeValue n arity symbols S Gamma (argumentChildValue value)]) =
    targetRepresentativeValue n arity symbols S Gamma value := by
  cases hd : decodeUniverse n arity symbols S Gamma value with
  | none => simp [sourceValidityValue,rawCarrierTest,hd] at hs
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
      exact typedApplicationCombine n arity symbols S hc Gamma table data h _ _ f a hf ha
    | _ => simp [tagValue,payloadValue,packedNumber,termCode,codeNumber] at ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationApplicationProof
