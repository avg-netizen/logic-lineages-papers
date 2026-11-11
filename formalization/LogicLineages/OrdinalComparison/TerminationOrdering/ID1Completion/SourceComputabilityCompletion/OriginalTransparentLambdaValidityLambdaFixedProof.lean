module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityLambdaDecoderProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityLambdaFixedProof
open Source NumberedLeastCodeRepresentative
open InternalOriginalStepGuard
open OriginalHereditaryValidity OriginalTransparentLambdaValidity
open OriginalTransparentLambdaValidityLambdaDecoderProof

theorem fixedLambdaAcceptance (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (sigma : Ty)
    (value : Nat) (ht : tagValue value = 1) (hd : typeNumber sigma = domainValue value) :
    (targetValidityValue n arity Gamma value = 1 ↔
      lambdaShapeValue value = 1 ∧
      targetValidityValue n arity (sigma :: Gamma) (lambdaBodyValue value) = 1) ∧
    (sourceValidityValue n arity symbols S Gamma value = 1 ↔
      lambdaShapeValue value = 1 ∧
      InternalStructuralEndpointGuard.membershipValue S (resultTypeValue value) = 1 ∧
      InternalStructuralEndpointGuard.membershipValue S (domainValue value) = 1 ∧
      sourceValidityValue n arity symbols S (sigma :: Gamma) (lambdaBodyValue value) = 1) := by
  by_cases hs : lambdaShapeValue value = 1
  · obtain ⟨tau,_,he⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal (lambdaCodomainValue value)
    have hshape : resultTypeValue value =
        Nat.succ (Nat.pair (domainValue value) (lambdaCodomainValue value)) := by
      simpa [lambdaShapeValue] using hs
    have hr : resultTypeValue value = typeNumber (.arrow sigma tau) := by
      simpa [typeNumber,hd,he,Nat.add_comm 1] using hshape
    have hp :
        Nat.pair (typeNumber (.arrow sigma tau))
          (Nat.pair 1 (Nat.pair (typeNumber sigma) (lambdaBodyPayloadValue value))) = value := by
      simpa [typeNumber,hd,he,Nat.add_comm 1] using lambdaReconstruction value ht hs
    have hb : lambdaBodyValue value = Nat.pair (typeNumber tau) (lambdaBodyPayloadValue value) := by
      rw [lambdaBodyValue,← he]
    have ha := typedLambdaAcceptance n arity symbols S Gamma sigma tau (lambdaBodyPayloadValue value)
    rw [hp,← hb] at ha
    rw [← hr,hd] at ha
    simpa [hs] using ha
  · have hnt : targetValidityValue n arity Gamma value ≠ 1 := by
      intro ha
      exact hs (shapeOfTarget n arity Gamma value ht ha)
    have hns : sourceValidityValue n arity symbols S Gamma value ≠ 1 := by
      intro ha
      exact hnt (fixedSourceImpliesTarget n arity symbols S Gamma value ha)
    simp [hs,hnt,hns]

/-- Full outputs, not merely acceptance equivalence, at an arbitrary original
fixed Gamma and finite window. The raw lambda need not be well-typed. -/
theorem fixedLambdaEquations (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (sigma : Ty)
    (value : Nat) (ht : tagValue value = 1) (hd : typeNumber sigma = domainValue value) :
    (targetValidityValue n arity Gamma value =
      if lambdaShapeValue value = 1 ∧
        targetValidityValue n arity (sigma :: Gamma) (lambdaBodyValue value) = 1 then 1 else 0) ∧
    (sourceValidityValue n arity symbols S Gamma value =
      if lambdaShapeValue value = 1 ∧
        InternalStructuralEndpointGuard.membershipValue S (resultTypeValue value) = 1 ∧
        InternalStructuralEndpointGuard.membershipValue S (domainValue value) = 1 ∧
        sourceValidityValue n arity symbols S (sigma :: Gamma) (lambdaBodyValue value) = 1
        then 1 else 0) := by
  have ha := fixedLambdaAcceptance n arity symbols S Gamma sigma value ht hd
  constructor
  · split
    · next h => exact ha.1.mpr h
    · next h =>
        exact InternalApplicationValidityStackDecoderProof.boolValueZero _ (fun he => h (ha.1.mp he))
  · split
    · next h => exact ha.2.mpr h
    · next h =>
        exact InternalApplicationValidityStackDecoderProof.boolValueZero _ (fun he => h (ha.2.mp he))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityLambdaFixedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityLambdaFixedProof
