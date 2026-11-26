module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalLambdaSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLambdaPackedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification
open OriginalTransparentDecoderValidatorCollapsePackedProof
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The old packed source lambda exposes both memberships and the exact
original shape. The SAME G at the extended child supplies the root G back. -/
theorem sourceLambdaCoordinatesIff (H G : Program 1) (M W : Program 2)
    (packed parameter typ payload middle domain bodyPayload requestedDomain codomain
      child c gamma extended childParameterCode : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ payload)))
    (ht : Nonempty (Derivation body Gamma (StepPair payload (numeral 1) middle)))
    (hm : Nonempty (Derivation body Gamma (StepPair middle domain bodyPayload)))
    (hf : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain codomain)))
    (hchild : Nonempty (Derivation body Gamma (StepPair child codomain bodyPayload)))
    (hparam : Nonempty (Derivation body Gamma (StepPair parameter c gamma)))
    (he : Nonempty (Derivation body Gamma (StepCons extended domain gamma)))
    (hchildParam : Nonempty (Derivation body Gamma (StepPair childParameterCode c extended))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter).iff
        ((graph2 M (numeral 1) typ c ⊓
          (graph2 M (numeral 1) domain c ⊓
            ((equal typ (numeral 0)).not ⊓ equal requestedDomain domain))) ⊓
          graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) child childParameterCode))) := by
  let S := OriginalUniverseDecoder.source H G M W
  let A := graph2 S (numeral 1) packed parameter
  let B := (graph2 M (numeral 1) typ c ⊓
    (graph2 M (numeral 1) domain c ⊓ ((equal typ (numeral 0)).not ⊓ equal requestedDomain domain))) ⊓
      graph2 S (numeral 1) child childParameterCode
  have hrec := OriginalUniverseDecoderInternalAcceptanceUnaryProof.lambdaIff
    H M W payload middle domain bodyPayload typ requestedDomain codomain gamma extended c ht hm hf he
  have forward : Nonempty (Derivation body (A :: Gamma) B) := by
    have fields := sourceFieldsElim H G M W packed parameter typ payload c gamma
      (addAssumption hp A) (addAssumption hparam A)
      (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have factors := iffForward (addAssumption hrec A) (andRight fields)
    have shape := andRight (andRight factors)
    have childSource := sourceFieldsIntro H G M W child childParameterCode codomain bodyPayload c extended
      (addAssumption hchild A) (addAssumption hchildParam A) (andLeft fields) (andRight (andRight shape))
    exact andIntro
      (andIntro (andLeft factors) (andIntro (andLeft (andRight factors))
        (andIntro (andLeft shape) (andLeft (andRight shape))))) childSource
  have backward : Nonempty (Derivation body (B :: Gamma) A) := by
    have h : Nonempty (Derivation body (B :: Gamma) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have root := andLeft h
    have shape := andRight (andRight root)
    have childFields := sourceFieldsElim H G M W child childParameterCode codomain bodyPayload c extended
      (addAssumption hchild B) (addAssumption hchildParam B) (andRight h)
    have accepted := iffBackward (addAssumption hrec B)
      (andIntro (andLeft root) (andIntro (andLeft (andRight root))
        (andIntro (andLeft shape) (andIntro (andRight shape) (andRight childFields)))))
    exact sourceFieldsIntro H G M W packed parameter typ payload c gamma
      (addAssumption hp B) (addAssumption hparam B) (andLeft childFields) accepted
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLambdaPackedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLambdaPackedProof
