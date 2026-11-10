module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerEvaluationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafGuardEvaluationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding
open NumberedNumericCarrier NumberedNumericStep ApplicationCertificateLift
open InternalApplicationStepPeel InternalParameterizedApplicationStepChecker
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original application-shaped edge and literal supplied lifted
certificate pass the actual parameterized peel guard. Only the source
application is confined; target validity remains unrestricted packed
validity, exactly as in the original endpoint. No child-step acceptance or
subtype-closure premise is needed for this native constructor calculation. -/
theorem liftedGuardAccept (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (endpoint : Program 6) (parameter : Nat)
    (calibrated : EndpointCalibratedAt n arity symbols S Gamma endpoint parameter)
    (sigma tau : Ty) (f g : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) (child : Nat)
    (hsource : InUniverse symbols S (.app f a)) :
    evaluate (guardP endpoint) (List.Vector.ofFn
      ![Nat.pair (packedNumber (⟨tau,.app f a⟩ : Packed (Fin n) arity Gamma))
          (Nat.pair (packedNumber (⟨tau,.app g a⟩ : Packed (Fin n) arity Gamma))
            (liftStep child)),parameter]) = 1 := by
  let state := Nat.pair (packedNumber (⟨tau,.app f a⟩ : Packed (Fin n) arity Gamma))
    (Nat.pair (packedNumber (⟨tau,.app g a⟩ : Packed (Fin n) arity Gamma)) (liftStep child))
  change evaluate (guardP endpoint) (List.Vector.ofFn ![state,parameter]) = 1
  rw [(InternalParameterizedApplicationStepCheckerEvaluationSupportProof.transitionCalibration
    n arity symbols S Gamma endpoint parameter calibrated state).1]
  have hshape : shape (view state) = true := by
    simp [state,shape,view,packedNumber,termCode,codeNumber,liftStep,positionNumber,
      show Nat.pair 1 0 = 2 from rfl]
  have hinputs : endpointInputs (view state) = List.Vector.ofFn
      ![typeNumber sigma,typeNumber tau,
        packedNumber (⟨.arrow sigma tau,f⟩ : Packed (Fin n) arity Gamma),
        packedNumber (⟨.arrow sigma tau,g⟩ : Packed (Fin n) arity Gamma),
        packedNumber (⟨sigma,a⟩ : Packed (Fin n) arity Gamma)] := by
    simp [state,endpointInputs,view,packedNumber,termCode,codeNumber,typeNumber]
  have hf : InUniverse symbols S f := ⟨hsource.1.2.1,hsource.2.1⟩
  have ha : InUniverse symbols S a := ⟨hsource.1.2.2,hsource.2.2⟩
  have hdf := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
    (packedNumber (⟨.arrow sigma tau,f⟩ : Packed (Fin n) arity Gamma))
    ⟨.arrow sigma tau,f⟩).mpr ⟨rfl,hf⟩
  have hdg := NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma
    (⟨.arrow sigma tau,g⟩ : Packed (Fin n) arity Gamma)
  have hda := (NumberedNumericCarrierProof.numericUniverseDecode n arity symbols S Gamma
    (packedNumber (⟨sigma,a⟩ : Packed (Fin n) arity Gamma))
    ⟨sigma,a⟩).mpr ⟨rfl,ha⟩
  have hm : tau ∈ S := hsource.1.1
  have he : endpointValue n arity symbols S Gamma (endpointInputs (view state)) = 1 := by
    rw [hinputs]
    simp [endpointValue,NumberedNumericDecodingSupportProof.typeRoundTrip,hdf,hdg,hda,hm]
  simp [guardValue,hshape,he]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafGuardEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafGuardEvaluationProof
