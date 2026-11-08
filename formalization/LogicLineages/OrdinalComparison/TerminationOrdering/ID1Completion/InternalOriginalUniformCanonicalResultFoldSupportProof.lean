module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier
open NumberedQuotientApplication
open InternalOriginalStepGuard (sourceValidityValue)
open InternalQuotientEdgeChecker (targetRepresentativeValue)
open InternalParameterizedCanonicalResultFold (Data validity rootGuard leaf rawApplicationAt combine)
open InternalOriginalUniformParameterLeaves (parameterCode)
open InternalOriginalUniformDescentSelectionEvaluationProof
open InternalApplicationValidityStack InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof
open InternalRepresentativeFoldCalibrationSupportProof (targetOnPacked applicationSelectors)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The literal guard tests source validity first, at the unchanged
parameter. Its other tests are retained in the AST; no equivalence with
source validity on nonapplications is asserted or required. -/
theorem rootGuardSource (data : Data) (value parameter : Nat)
    (h : evaluate (rootGuard data) (List.Vector.ofFn ![value,parameter]) = 1) :
    evaluate (validity data) (List.Vector.ofFn ![value,parameter]) = 1 := by
  rw [rootGuard,InternalApplicationStepPeelEvaluationSupportProof.conjunctionEvaluation] at h
  split at h
  · rename_i hh
    exact hh.1
  · exact False.elim (Nat.zero_ne_one h)

/-- The leaf is the same all-input original-fallback descent selection.
Malformed inputs and decoded terms outside the source universe are included. -/
theorem leafCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun tau => tau ∈ S)) (value : Nat) :
    evaluate (leaf data) (List.Vector.ofFn ![value,parameterCode symbols S Gamma table]) =
      targetRepresentativeValue n arity symbols S Gamma value :=
  actualOriginalUniformRepresentativeCalibration n arity data hc symbols S Gamma table hS value

/-- Apply the same D to the ORIGINAL raw application of whole child outputs.
The parameter is input four and is never packed into the raw term. -/
theorem combineCalibration (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun tau => tau ∈ S)) (d e fn arg : Nat) :
    evaluate (combine data)
      (List.Vector.ofFn ![d,e,fn,arg,parameterCode symbols S Gamma table]) =
      targetRepresentativeValue n arity symbols S Gamma
        (ApplicationCertificateLift.rawApplication d e fn arg) := by
  change evaluate (leaf data) (List.Vector.ofFn
    ![evaluate InternalApplicationCertificateConstructors.application
      (List.Vector.ofFn ![d,e,fn,arg]),parameterCode symbols S Gamma table]) = _
  rw [leafCalibration n arity data hc symbols S Gamma table hS,applicationEvaluation]
  rfl

/-- Original decoded representatives and original quotient application
congruence identify the actual combine on genuine typed universe children. -/
theorem typedApplicationCombine (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (symbols : List (Fin n)) (S : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S))
    (Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (sigma tau : Ty) (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma)
    (hf : InUniverse symbols S f) (ha : InUniverse symbols S a) :
    evaluate (combine data) (List.Vector.ofFn ![typeNumber sigma,typeNumber tau,
      representativeCode symbols S ⟨.arrow sigma tau,f⟩,
      representativeCode symbols S ⟨sigma,a⟩,parameterCode symbols S Gamma table]) =
      representativeCode symbols S (applicationPacked f a) := by
  obtain ⟨g,hg,hdg,hreg⟩ :=
    NumberedNumericApplicationSupportProof.decodedRepresentative n arity symbols S hS
      Gamma (.arrow sigma tau) f hf
  obtain ⟨b,hb,hdb,hreb⟩ :=
    NumberedNumericApplicationSupportProof.decodedRepresentative n arity symbols S hS
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
    n arity symbols S hS Gamma sigma tau g f b a hg hf hb ha hreg hreb
  rw [combineCalibration n arity data hc symbols S Gamma table hS,happ,targetOnPacked,he]

/-- Source-universe decoding of the original opened root supplies the
typed children used by original congruence. There is no canonical-input
assumption and no claim about a source-invalid application's children. -/
theorem openedRootCombine (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (symbols : List (Fin n)) (S : List Ty) (hS : SubtypeClosed (fun tau => tau ∈ S))
    (Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (value : Nat) (ht : tagValue value = 2)
    (hs : sourceValidityValue n arity symbols S Gamma value = 1) :
    evaluate (combine data) (List.Vector.ofFn ![domainValue value,resultTypeValue value,
      targetRepresentativeValue n arity symbols S Gamma (functionChildValue value),
      targetRepresentativeValue n arity symbols S Gamma (argumentChildValue value),
      parameterCode symbols S Gamma table]) =
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
      exact typedApplicationCombine n arity data hc symbols S hS Gamma table _ _ f a hf ha
    | _ => simp [tagValue,payloadValue,packedNumber,termCode,codeNumber] at ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldSupportProof
