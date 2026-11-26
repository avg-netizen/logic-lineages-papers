module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceLeafSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceOutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceRejectedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalLogicSyntaxProof
open OriginalTypedDecoderInternalRequestSyntaxProof OriginalTypedDecoderInternalDispatchSyntaxProof
open OriginalTypedDecoderInternalAcceptanceSyntaxProof OriginalTypedDecoderInternalAcceptanceBranchProof
open OriginalTypedDecoderInternalAcceptanceCheckerProof OriginalTypedDecoderInternalAcceptanceOutputProof
open OriginalTypedDecoderInternalAcceptanceLeafSupportProof
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
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem orRename {beta : Type} (p q : Formula alpha) (j : alpha → beta) :
    (p ⊔ q).relabel j = (p.relabel j) ⊔ (q.relabel j) := rfl

theorem termRejectedOutput (H : Program 1) (state work request raw tagCode payloadCode typCode gammaCode out : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gammaCode typCode raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw tagCode payloadCode)))
    (hb : Nonempty (Derivation body Gamma
      (equal tagCode (numeral 6) ⊔ (equal tagCode (numeral 7) ⊔ StepUnknownTag tagCode))))
    (ht : Nonempty (Derivation body Gamma (graph1 (transition H) out state))) :
    Nonempty (Derivation body Gamma (equal out z)) := by
  apply choiceCases hb
  · intro Delta inc he
    have hp' := pairTagTransport raw tagCode (numeral 6) payloadCode (weakenProof hp inc) he
    exact constantForward 0 out (Fin.cons state Fin.elim0)
      (termProgramForward H 6 state work request z out gammaCode typCode raw payloadCode
        (weakenProof hs inc) (weakenProof hc inc) (weakenProof hr inc) hp' (weakenProof ht inc))
  · intro Delta inc hrest
    have hs' := weakenProof hs inc
    have hc' := weakenProof hc inc
    have hr' := weakenProof hr inc
    have hp' := weakenProof hp inc
    have ht' := weakenProof ht inc
    apply choiceCases hrest
    · intro Theta inc' he
      have hp'' := pairTagTransport raw tagCode (numeral 7) payloadCode (weakenProof hp' inc') he
      exact constantForward 0 out (Fin.cons state Fin.elim0)
        (termProgramForward H 7 state work request z out gammaCode typCode raw payloadCode
          (weakenProof hs' inc') (weakenProof hc' inc') (weakenProof hr' inc') hp'' (weakenProof ht' inc'))
    · intro Theta inc' hn
      have hv := requestValues state work request z (numeral 0) gammaCode typCode raw tagCode payloadCode
        (weakenProof hs' inc') (weakenProof hc' inc') (weakenProof hr' inc') (weakenProof hp' inc')
      have hm := modeAtForward H state work request z out
        (weakenProof hs' inc') (weakenProof hc' inc') (weakenProof ht' inc')
      have hd := branchNumeralElim 0 0 mode _ (termDispatch H) out (Fin.cons state Fin.elim0) (hv 0) hm
      exact termUnknownForward H state out tagCode (hv 3) hn hd

theorem argumentsRejectedOutput (H : Program 1) (state work request raw tagCode payloadCode typCode gammaCode out : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) gammaCode typCode raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw tagCode payloadCode)))
    (hb : Nonempty (Derivation body Gamma
      ((equal tagCode (numeral 6)).not ⊓ (equal tagCode (numeral 7)).not)))
    (ht : Nonempty (Derivation body Gamma (graph1 (transition H) out state))) :
    Nonempty (Derivation body Gamma (equal out z)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hv := requestValues state work request z (numeral 1) gammaCode typCode raw tagCode payloadCode hs hc hr hp
  have hm := modeAtForward H state work request z out hs hc ht
  have h0 := branchNumeralElim 1 0 mode _ (termDispatch H) out xs (hv 0) hm
  have hd := branchNumeralElim 1 1 mode _ argumentsDispatch out xs (hv 0) h0
  have h6 := sameNoElim tag (constant 1 6) nilStep _ out tagCode (numeral 6) xs
    (hv 3) (constantValue 6 xs) (andLeft hb) hd
  have h7 := sameNoElim tag (constant 1 7) consStep _ out tagCode (numeral 7) xs
    (hv 3) (constantValue 7 xs) (andRight hb) h6
  exact constantForward 0 out xs h7

theorem rejectionRename {beta : Type} (p : Formula alpha) (j : alpha → beta) :
    (p.not).relabel j = (p.relabel j).not := rfl

theorem termRejectedAt (H : Program 1) (state work request raw tagCode payloadCode typCode gammaCode : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gammaCode typCode raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw tagCode payloadCode)))
    (hb : Nonempty (Derivation body Gamma (equal tagCode (numeral 6) ⊔ (equal tagCode (numeral 7) ⊔ StepUnknownTag tagCode))))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H typCode raw gammaCode))) :
    Nonempty (Derivation body Gamma (⊥ : Formula alpha)) := by
  apply outputCases H 0 state work request gammaCode typCode raw _ hs hc hr ha
  intro beta j Delta out hj ht haccepted
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
  exact acceptedRejectImpossible H out
    (termRejectedOutput H (state.relabel j) (work.relabel j) (request.relabel j) (raw.relabel j)
      (tagCode.relabel j) (payloadCode.relabel j) (typCode.relabel j) (gammaCode.relabel j) out
      hs' hc' hr' hp' hb' ht) haccepted

theorem termRejected (H : Program 1) (raw tagCode payloadCode typCode gammaCode : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair raw tagCode payloadCode)))
    (hb : Nonempty (Derivation body Gamma (equal tagCode (numeral 6) ⊔ (equal tagCode (numeral 7) ⊔ StepUnknownTag tagCode))))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H typCode raw gammaCode))) :
    Nonempty (Derivation body Gamma (⊥ : Formula alpha)) := by
  apply singletonCases 0 typCode raw gammaCode _
  intro beta j Delta state work request hj hs hc hr
  have hp' := renameInto hp j Delta hj
  rw [stepPairRename] at hp'
  have hb' := renameInto hb j Delta hj
  simp only [orRename,stepUnknownTagRename,equalRename,numeralRename] at hb'
  have ha' := renameInto ha j Delta hj
  rw [termAcceptedRename] at ha'
  exact termRejectedAt H state work request (raw.relabel j) (tagCode.relabel j)
    (payloadCode.relabel j) (typCode.relabel j) (gammaCode.relabel j) hs hc hr hp' hb' ha'

theorem argumentsRejectedAt (H : Program 1) (state work request raw tagCode payloadCode typCode gammaCode : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) gammaCode typCode raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw tagCode payloadCode)))
    (hb : Nonempty (Derivation body Gamma ((equal tagCode (numeral 6)).not ⊓ (equal tagCode (numeral 7)).not)))
    (ha : Nonempty (Derivation body Gamma (ArgumentsAccepted H typCode raw gammaCode))) :
    Nonempty (Derivation body Gamma (⊥ : Formula alpha)) := by
  apply outputCases H 1 state work request gammaCode typCode raw _ hs hc hr ha
  intro beta j Delta out hj ht haccepted
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
  exact acceptedRejectImpossible H out
    (argumentsRejectedOutput H (state.relabel j) (work.relabel j) (request.relabel j) (raw.relabel j)
      (tagCode.relabel j) (payloadCode.relabel j) (typCode.relabel j) (gammaCode.relabel j) out
      hs' hc' hr' hp' hb' ht) haccepted

theorem argumentsRejected (H : Program 1) (raw tagCode payloadCode typCode gammaCode : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair raw tagCode payloadCode)))
    (hb : Nonempty (Derivation body Gamma ((equal tagCode (numeral 6)).not ⊓ (equal tagCode (numeral 7)).not)))
    (ha : Nonempty (Derivation body Gamma (ArgumentsAccepted H typCode raw gammaCode))) :
    Nonempty (Derivation body Gamma (⊥ : Formula alpha)) := by
  apply singletonCases 1 typCode raw gammaCode _
  intro beta j Delta state work request hj hs hc hr
  have hp' := renameInto hp j Delta hj
  rw [stepPairRename] at hp'
  have hb' := renameInto hb j Delta hj
  simp only [conjunctionRename,rejectionRename,equalRename,numeralRename] at hb'
  have ha' := renameInto ha j Delta hj
  rw [argumentsAcceptedRename] at ha'
  exact argumentsRejectedAt H state work request (raw.relabel j) (tagCode.relabel j)
    (payloadCode.relabel j) (typCode.relabel j) (gammaCode.relabel j) hs hc hr hp' hb' ha'

theorem actualOriginalTypedInternalRejectedTags :
    OriginalTypedDecoderInternalAcceptanceTargets.ActualOriginalTypedInternalRejectedTags := by
  constructor
  · intro body H alpha raw tagCode payloadCode typCode gammaCode
    let A := StepPair raw tagCode payloadCode ⊓
      (equal tagCode (numeral 6) ⊔ (equal tagCode (numeral 7) ⊔ StepUnknownTag tagCode))
    let P := TermAccepted H typCode raw gammaCode
    have hh : Nonempty (Derivation body [P,A] A) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    obtain ⟨h⟩ := termRejected H raw tagCode payloadCode typCode gammaCode (andLeft hh) (andRight hh)
      (show Nonempty (Derivation body [P,A] P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩
  · intro body H alpha raw tagCode payloadCode typCode gammaCode
    let A := StepPair raw tagCode payloadCode ⊓
      ((equal tagCode (numeral 6)).not ⊓ (equal tagCode (numeral 7)).not)
    let P := ArgumentsAccepted H typCode raw gammaCode
    have hh : Nonempty (Derivation body [P,A] A) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    obtain ⟨h⟩ := argumentsRejected H raw tagCode payloadCode typCode gammaCode (andLeft hh) (andRight hh)
      (show Nonempty (Derivation body [P,A] P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceRejectedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceRejectedProof
