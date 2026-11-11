module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceLeafSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceRejectedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceRejectedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalLogicSyntaxProof
open OriginalTypedDecoderInternalRequestSyntaxProof OriginalTypedDecoderInternalDispatchSyntaxProof
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof OriginalUniverseDecoderInternalAcceptanceBranchProof
open OriginalTypedDecoderInternalAcceptanceCheckerProof OriginalUniverseDecoderInternalAcceptanceOutputProof
open OriginalUniverseDecoderInternalAcceptanceLeafSupportProof
open OriginalTypedDecoderInternalBranchProof OriginalTypedDecoderInternalTagBranchProof
open OriginalTypedDecoderInternalModeProof
open OriginalTypedDecoderInternalFuelDecreaseDispatchProof (pairTagTransport)
open OriginalTypedDecoderInternalFuelDecreaseLeafProof (choiceCases weakenProof)
open OriginalTypedDecoderInternalFuelSupportProof (withHyp)
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (branchNumeralElim)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedDecoderInternalAcceptanceRejectedProof (orRename rejectionRename termRejectedOutput argumentsRejectedOutput)
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem termRejectedAt (H : Program 1) (M W : Program 2) (state work request raw tagCode payloadCode typCode gammaCode c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gammaCode typCode raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw tagCode payloadCode)))
    (hb : Nonempty (Derivation body Gamma (equal tagCode (numeral 6) ⊔ (equal tagCode (numeral 7) ⊔ StepUnknownTag tagCode))))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H M W typCode raw gammaCode c))) :
    Nonempty (Derivation body Gamma (⊥ : Formula alpha)) := by
  apply outputCases H M W 0 state work request gammaCode typCode raw c _ hs hc hr ha
  intro beta j Delta out hj hg ht haccepted
  have hs' := renameInto hs j Delta hj
  rw [stepLiveRename] at hs'
  have hc' := renameInto hc j Delta hj
  simp only [stepConsRename,zRelabel] at hc'
  have hr' := renameInto hr j Delta hj
  simp only [stepRequestRename,numeralRename] at hr'
  have hp' := renameInto hp j Delta hj
  rw [stepPairRename] at hp'
  have hb' := renameInto hb j Delta hj
  simp only [orRename,stepUnknownTagRename,equalRename,numeralRename] at hb'
  exact acceptedRejectImpossible H M W out (c.relabel j)
    (termRejectedOutput H (state.relabel j) (work.relabel j) (request.relabel j) (raw.relabel j)
      (tagCode.relabel j) (payloadCode.relabel j) (typCode.relabel j) (gammaCode.relabel j) out
      hs' hc' hr' hp' hb' ht) haccepted

theorem termRejected (H : Program 1) (M W : Program 2) (raw tagCode payloadCode typCode gammaCode c : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair raw tagCode payloadCode)))
    (hb : Nonempty (Derivation body Gamma (equal tagCode (numeral 6) ⊔ (equal tagCode (numeral 7) ⊔ StepUnknownTag tagCode))))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H M W typCode raw gammaCode c))) :
    Nonempty (Derivation body Gamma (⊥ : Formula alpha)) := by
  apply singletonCases 0 typCode raw gammaCode _
  intro beta j Delta state work request hj hs hc hr
  have hp' := renameInto hp j Delta hj
  rw [stepPairRename] at hp'
  have hb' := renameInto hb j Delta hj
  simp only [orRename,stepUnknownTagRename,equalRename,numeralRename] at hb'
  have ha' := renameInto ha j Delta hj
  rw [termAcceptedRename] at ha'
  exact termRejectedAt H M W state work request (raw.relabel j) (tagCode.relabel j)
    (payloadCode.relabel j) (typCode.relabel j) (gammaCode.relabel j) (c.relabel j) hs hc hr hp' hb' ha'

theorem argumentsRejectedAt (H : Program 1) (M W : Program 2) (state work request raw tagCode payloadCode typCode gammaCode c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) gammaCode typCode raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw tagCode payloadCode)))
    (hb : Nonempty (Derivation body Gamma ((equal tagCode (numeral 6)).not ⊓ (equal tagCode (numeral 7)).not)))
    (ha : Nonempty (Derivation body Gamma (ArgumentsAccepted H M W typCode raw gammaCode c))) :
    Nonempty (Derivation body Gamma (⊥ : Formula alpha)) := by
  apply outputCases H M W 1 state work request gammaCode typCode raw c _ hs hc hr ha
  intro beta j Delta out hj hg ht haccepted
  have hs' := renameInto hs j Delta hj
  rw [stepLiveRename] at hs'
  have hc' := renameInto hc j Delta hj
  simp only [stepConsRename,zRelabel] at hc'
  have hr' := renameInto hr j Delta hj
  simp only [stepRequestRename,numeralRename] at hr'
  have hp' := renameInto hp j Delta hj
  rw [stepPairRename] at hp'
  have hb' := renameInto hb j Delta hj
  simp only [conjunctionRename,rejectionRename,equalRename,numeralRename] at hb'
  exact acceptedRejectImpossible H M W out (c.relabel j)
    (argumentsRejectedOutput H (state.relabel j) (work.relabel j) (request.relabel j) (raw.relabel j)
      (tagCode.relabel j) (payloadCode.relabel j) (typCode.relabel j) (gammaCode.relabel j) out
      hs' hc' hr' hp' hb' ht) haccepted

theorem argumentsRejected (H : Program 1) (M W : Program 2) (raw tagCode payloadCode typCode gammaCode c : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair raw tagCode payloadCode)))
    (hb : Nonempty (Derivation body Gamma ((equal tagCode (numeral 6)).not ⊓ (equal tagCode (numeral 7)).not)))
    (ha : Nonempty (Derivation body Gamma (ArgumentsAccepted H M W typCode raw gammaCode c))) :
    Nonempty (Derivation body Gamma (⊥ : Formula alpha)) := by
  apply singletonCases 1 typCode raw gammaCode _
  intro beta j Delta state work request hj hs hc hr
  have hp' := renameInto hp j Delta hj
  rw [stepPairRename] at hp'
  have hb' := renameInto hb j Delta hj
  simp only [conjunctionRename,rejectionRename,equalRename,numeralRename] at hb'
  have ha' := renameInto ha j Delta hj
  rw [argumentsAcceptedRename] at ha'
  exact argumentsRejectedAt H M W state work request (raw.relabel j) (tagCode.relabel j)
    (payloadCode.relabel j) (typCode.relabel j) (gammaCode.relabel j) (c.relabel j) hs hc hr hp' hb' ha'

theorem actualOriginalUniverseInternalRejectedTags :
    OriginalUniverseDecoderInternalAcceptanceTargets.ActualOriginalUniverseInternalRejectedTags := by
  constructor
  · intro body H M W alpha raw tagCode payloadCode typCode gammaCode c
    let A := StepPair raw tagCode payloadCode ⊓
      (equal tagCode (numeral 6) ⊔ (equal tagCode (numeral 7) ⊔ StepUnknownTag tagCode))
    let P := TermAccepted H M W typCode raw gammaCode c
    have hh : Nonempty (Derivation body [P,A] A) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    obtain ⟨h⟩ := termRejected H M W raw tagCode payloadCode typCode gammaCode c (andLeft hh) (andRight hh)
      (show Nonempty (Derivation body [P,A] P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩
  · intro body H M W alpha raw tagCode payloadCode typCode gammaCode c
    let A := StepPair raw tagCode payloadCode ⊓
      ((equal tagCode (numeral 6)).not ⊓ (equal tagCode (numeral 7)).not)
    let P := ArgumentsAccepted H M W typCode raw gammaCode c
    have hh : Nonempty (Derivation body [P,A] A) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    obtain ⟨h⟩ := argumentsRejected H M W raw tagCode payloadCode typCode gammaCode c (andLeft hh) (andRight hh)
      (show Nonempty (Derivation body [P,A] P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceRejectedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceRejectedProof
