module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBinaryLocalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceUnaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel OriginalTypedDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalLogicSyntaxProof
open OriginalTypedDecoderInternalRequestSyntaxProof OriginalTypedDecoderInternalBinarySyntaxProof
open OriginalTypedDecoderInternalAcceptanceSyntaxProof OriginalTypedDecoderInternalAcceptanceStateProof
open OriginalTypedDecoderInternalAcceptanceBranchCasesProof OriginalTypedDecoderInternalAcceptanceBranchProof
open OriginalTypedDecoderInternalAcceptanceCheckerProof OriginalTypedDecoderInternalAcceptanceOutputProof
open OriginalTypedDecoderInternalAcceptancePushTwoProof OriginalTypedDecoderInternalAcceptanceBinaryLocalProof
open OriginalTypedDecoderInternalAcceptanceUnaryLocalProof
open OriginalTypedDecoderInternalAcceptanceUnaryProof (notRename singletonVectorRename)
open OriginalTypedDecoderInternalApplicationSyntaxProof OriginalTypedDecoderInternalNumberedSyntaxProof
open OriginalTypedDecoderInternalConsSyntaxProof
open OriginalTypedDecoderInternalFuelSupportProof (withHyp)
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem applicationForwardAt (H : Program 1) (state work request raw payload domain fn arg typ arrow gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 2) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain fn arg)))
    (h2 : Nonempty (Derivation body Gamma (StepCons arrow domain typ)))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H typ raw gamma))) :
    Nonempty (Derivation body Gamma (TermAccepted H arrow fn gamma ⊓ (TermAccepted H domain arg gamma))) := by
  apply outputCases H 0 state work request gamma typ raw _ hs hc hr ha
  intro beta j Delta out hj ht haccepted
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename]
  have hs' := renameInto hs j Delta hj
  rw [stepLiveRename] at hs'
  have hc' := renameInto hc j Delta hj
  simp only [stepConsRename,zRelabel] at hc'
  have hr' := renameInto hr j Delta hj
  simp only [stepRequestRename,numeralRename] at hr'
  have h0' := renameInto h0 j Delta hj
  simp only [stepPairRename,numeralRename] at h0'
  have h1' := renameInto h1 j Delta hj
  simp only [stepBinaryPayloadRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [stepConsRename] at h2'
  have hv := requestValues (state.relabel j) (work.relabel j) (request.relabel j) z
    (numeral 0) (gamma.relabel j) (typ.relabel j) (raw.relabel j) (numeral 2)
    (payload.relabel j) hs' hc' hr' h0'
  have hlocal := termProgramForward H 2 (state.relabel j) (work.relabel j) (request.relabel j) z
    out (gamma.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) hs' hc' hr' h0' ht
  have hg := applicationPushAt (state.relabel j) out (gamma.relabel j) (typ.relabel j) (payload.relabel j) (domain.relabel j) (fn.relabel j) (arg.relabel j) (arrow.relabel j) z (hv 1) (hv 2) (hv 4) (hv 5) h1' h2' hlocal
  have hchild := pushTwoAccepted H 0 0 out (gamma.relabel j) (arrow.relabel j) (fn.relabel j) (gamma.relabel j) (domain.relabel j) (arg.relabel j) hg haccepted
  exact hchild

theorem applicationBackwardAt (H : Program 1) (state work request raw payload domain fn arg typ arrow gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 2) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain fn arg)))
    (h2 : Nonempty (Derivation body Gamma (StepCons arrow domain typ)))
    (hq : Nonempty (Derivation body Gamma (TermAccepted H arrow fn gamma ⊓ (TermAccepted H domain arg gamma)))) :
    Nonempty (Derivation body Gamma (TermAccepted H typ raw gamma)) := by
  apply acceptedPushTwoCases H 0 0 gamma arrow fn gamma domain arg _
    (andLeft hq) (andRight hq)
  intro beta j Delta out hj hpush haccepted
  rw [termAcceptedRename]
  have hs' := renameInto hs j Delta hj
  rw [stepLiveRename] at hs'
  have hc' := renameInto hc j Delta hj
  simp only [stepConsRename,zRelabel] at hc'
  have hr' := renameInto hr j Delta hj
  simp only [stepRequestRename,numeralRename] at hr'
  have h0' := renameInto h0 j Delta hj
  simp only [stepPairRename,numeralRename] at h0'
  have h1' := renameInto h1 j Delta hj
  simp only [stepBinaryPayloadRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [stepConsRename] at h2'
  have hbranch := stepApplicationIntro out (gamma.relabel j) (typ.relabel j) (payload.relabel j) z
    (![ (domain.relabel j),(fn.relabel j),(arg.relabel j),(arrow.relabel j) ] : Fin 4 → OTerm beta)
    (andIntro h1' (andIntro h2' (hpush)))
  exact termBranchIntro H 2 (state.relabel j) (work.relabel j) (request.relabel j) out
    (gamma.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) hs' hc' hr' h0' hbranch haccepted

theorem applicationAt (H : Program 1) (state work request raw payload domain fn arg typ arrow gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 2) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain fn arg)))
    (h2 : Nonempty (Derivation body Gamma (StepCons arrow domain typ))) :
    Nonempty (Derivation body Gamma ((TermAccepted H typ raw gamma).iff (TermAccepted H arrow fn gamma ⊓ (TermAccepted H domain arg gamma)))) := by
  let P := TermAccepted H typ raw gamma
  let Q := TermAccepted H arrow fn gamma ⊓ (TermAccepted H domain arg gamma)
  obtain ⟨hf⟩ := applicationForwardAt H state work request raw payload domain fn arg typ arrow gamma
    (withHyp hs P) (withHyp hc P) (withHyp hr P) (withHyp h0 P) (withHyp h1 P) (withHyp h2 P)
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := applicationBackwardAt H state work request raw payload domain fn arg typ arrow gamma
    (withHyp hs Q) (withHyp hc Q) (withHyp hr Q) (withHyp h0 Q) (withHyp h1 Q) (withHyp h2 Q)
    (show Nonempty (Derivation body (Q :: Gamma) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem applicationIff (H : Program 1) (raw payload domain fn arg typ arrow gamma : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 2) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain fn arg)))
    (h2 : Nonempty (Derivation body Gamma (StepCons arrow domain typ))) :
    Nonempty (Derivation body Gamma ((TermAccepted H typ raw gamma).iff (TermAccepted H arrow fn gamma ⊓ (TermAccepted H domain arg gamma)))) := by
  apply singletonCases 0 typ raw gamma _
  intro beta j Delta state work request hj hs hc hr
  change Nonempty (Derivation body Delta
    (((TermAccepted H typ raw gamma).relabel j).iff ((TermAccepted H arrow fn gamma ⊓ (TermAccepted H domain arg gamma)).relabel j)))
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename]
  have h0' := renameInto h0 j Delta hj
  simp only [stepPairRename,numeralRename] at h0'
  have h1' := renameInto h1 j Delta hj
  simp only [stepBinaryPayloadRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [stepConsRename] at h2'
  exact applicationAt H state work request (raw.relabel j) (payload.relabel j) (domain.relabel j) (fn.relabel j) (arg.relabel j) (typ.relabel j) (arrow.relabel j) (gamma.relabel j) hs hc hr h0' h1' h2'

theorem actualOriginalTypedInternalApplicationAcceptance :
    OriginalTypedDecoderInternalAcceptanceTargets.ActualOriginalTypedInternalApplicationAcceptance := by
  intro body H alpha raw payload domain fn arg typ arrow gamma
  let A := StepPair raw (numeral 2) payload ⊓ (StepBinaryPayload payload domain fn arg ⊓ (StepCons arrow domain typ))
  have hh : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := applicationIff H raw payload domain fn arg typ arrow gamma
    (andLeft (hh)) (andLeft (andRight (hh))) (andRight (andRight (hh)))
  exact ⟨Derivation.implicationIntroduction h⟩

theorem numberedForwardAt (H : Program 1) (state work request raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 5) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepNumberedPayload payload label head recorded base extraTypes extras)))
    (h2 : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (h3 : Nonempty (Derivation body Gamma (StepArrowFields headData headResult baseTypes)))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H typ raw gamma))) :
    Nonempty (Derivation body Gamma ((equal headData z).not ⊓ (equal recorded typ ⊓ (ArgumentsAccepted H baseTypes base gamma ⊓ (ArgumentsAccepted H extraTypes extras gamma))))) := by
  apply outputCases H 0 state work request gamma typ raw _ hs hc hr ha
  intro beta j Delta out hj ht haccepted
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename]
  have hs' := renameInto hs j Delta hj
  rw [stepLiveRename] at hs'
  have hc' := renameInto hc j Delta hj
  simp only [stepConsRename,zRelabel] at hc'
  have hr' := renameInto hr j Delta hj
  simp only [stepRequestRename,numeralRename] at hr'
  have h0' := renameInto h0 j Delta hj
  simp only [stepPairRename,numeralRename] at h0'
  have h1' := renameInto h1 j Delta hj
  simp only [stepNumberedPayloadRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [programRename,singletonVectorRename] at h2'
  have h3' := renameInto h3 j Delta hj
  simp only [stepArrowFieldsRename] at h3'
  have hv := requestValues (state.relabel j) (work.relabel j) (request.relabel j) z
    (numeral 0) (gamma.relabel j) (typ.relabel j) (raw.relabel j) (numeral 5)
    (payload.relabel j) hs' hc' hr' h0'
  have hlocal := termProgramForward H 5 (state.relabel j) (work.relabel j) (request.relabel j) z
    out (gamma.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) hs' hc' hr' h0' ht
  have hg := numberedGuardAt H (state.relabel j) out (gamma.relabel j) (typ.relabel j) (payload.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j) (base.relabel j) (extraTypes.relabel j) (extras.relabel j) (headData.relabel j) (headResult.relabel j) (baseTypes.relabel j) z (hv 1) (hv 2) (hv 4) (hv 5) h1' h2' h3' hlocal
  have hgood := acceptedGuard H out (headData.relabel j) (recorded.relabel j) (typ.relabel j) _ hg haccepted
  have hchild := pushTwoAccepted H 1 1 out (gamma.relabel j) (baseTypes.relabel j) (base.relabel j) (gamma.relabel j) (extraTypes.relabel j) (extras.relabel j) (andRight (andRight hgood)) haccepted
  exact andIntro (andLeft hgood) (andIntro (andLeft (andRight hgood)) hchild)

theorem numberedBackwardAt (H : Program 1) (state work request raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 5) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepNumberedPayload payload label head recorded base extraTypes extras)))
    (h2 : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (h3 : Nonempty (Derivation body Gamma (StepArrowFields headData headResult baseTypes)))
    (hq : Nonempty (Derivation body Gamma ((equal headData z).not ⊓ (equal recorded typ ⊓ (ArgumentsAccepted H baseTypes base gamma ⊓ (ArgumentsAccepted H extraTypes extras gamma)))))) :
    Nonempty (Derivation body Gamma (TermAccepted H typ raw gamma)) := by
  apply acceptedPushTwoCases H 1 1 gamma baseTypes base gamma extraTypes extras _
    (andLeft (andRight (andRight hq))) (andRight (andRight (andRight hq)))
  intro beta j Delta out hj hpush haccepted
  rw [termAcceptedRename]
  have hs' := renameInto hs j Delta hj
  rw [stepLiveRename] at hs'
  have hc' := renameInto hc j Delta hj
  simp only [stepConsRename,zRelabel] at hc'
  have hr' := renameInto hr j Delta hj
  simp only [stepRequestRename,numeralRename] at hr'
  have h0' := renameInto h0 j Delta hj
  simp only [stepPairRename,numeralRename] at h0'
  have h1' := renameInto h1 j Delta hj
  simp only [stepNumberedPayloadRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [programRename,singletonVectorRename] at h2'
  have h3' := renameInto h3 j Delta hj
  simp only [stepArrowFieldsRename] at h3'
  have hq' := renameInto hq j Delta hj
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename] at hq'
  have hguard : Nonempty (Derivation body Delta
      (((equal (headData.relabel j) z).not ⊓ (equal (recorded.relabel j) (typ.relabel j) ⊓
        StepPushTwo out (numeral 1) (gamma.relabel j) (baseTypes.relabel j) (base.relabel j) (numeral 1) (gamma.relabel j) (extraTypes.relabel j) (extras.relabel j) z)) ⊔
        ((equal (headData.relabel j) z ⊔ (equal (recorded.relabel j) (typ.relabel j)).not) ⊓ equal out z))) := by
    obtain ⟨h⟩ := andIntro (andLeft hq') (andIntro (andLeft (andRight hq')) hpush)
    exact ⟨InternalQuotientComparisonProof.orLeft h⟩
  have hbranch := stepNumberedIntro H out (gamma.relabel j) (typ.relabel j) (payload.relabel j) z
    (![ (label.relabel j),(head.relabel j),(recorded.relabel j),(base.relabel j),(extraTypes.relabel j),(extras.relabel j),(headData.relabel j),(headResult.relabel j),(baseTypes.relabel j) ] : Fin 9 → OTerm beta)
    (andIntro h1' (andIntro h2' (andIntro h3' (hguard))))
  exact termBranchIntro H 5 (state.relabel j) (work.relabel j) (request.relabel j) out
    (gamma.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) hs' hc' hr' h0' hbranch haccepted

theorem numberedAt (H : Program 1) (state work request raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 5) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepNumberedPayload payload label head recorded base extraTypes extras)))
    (h2 : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (h3 : Nonempty (Derivation body Gamma (StepArrowFields headData headResult baseTypes))) :
    Nonempty (Derivation body Gamma ((TermAccepted H typ raw gamma).iff ((equal headData z).not ⊓ (equal recorded typ ⊓ (ArgumentsAccepted H baseTypes base gamma ⊓ (ArgumentsAccepted H extraTypes extras gamma)))))) := by
  let P := TermAccepted H typ raw gamma
  let Q := (equal headData z).not ⊓ (equal recorded typ ⊓ (ArgumentsAccepted H baseTypes base gamma ⊓ (ArgumentsAccepted H extraTypes extras gamma)))
  obtain ⟨hf⟩ := numberedForwardAt H state work request raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma
    (withHyp hs P) (withHyp hc P) (withHyp hr P) (withHyp h0 P) (withHyp h1 P) (withHyp h2 P) (withHyp h3 P)
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := numberedBackwardAt H state work request raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma
    (withHyp hs Q) (withHyp hc Q) (withHyp hr Q) (withHyp h0 Q) (withHyp h1 Q) (withHyp h2 Q) (withHyp h3 Q)
    (show Nonempty (Derivation body (Q :: Gamma) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem numberedIff (H : Program 1) (raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 5) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepNumberedPayload payload label head recorded base extraTypes extras)))
    (h2 : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (h3 : Nonempty (Derivation body Gamma (StepArrowFields headData headResult baseTypes))) :
    Nonempty (Derivation body Gamma ((TermAccepted H typ raw gamma).iff ((equal headData z).not ⊓ (equal recorded typ ⊓ (ArgumentsAccepted H baseTypes base gamma ⊓ (ArgumentsAccepted H extraTypes extras gamma)))))) := by
  apply singletonCases 0 typ raw gamma _
  intro beta j Delta state work request hj hs hc hr
  change Nonempty (Derivation body Delta
    (((TermAccepted H typ raw gamma).relabel j).iff (((equal headData z).not ⊓ (equal recorded typ ⊓ (ArgumentsAccepted H baseTypes base gamma ⊓ (ArgumentsAccepted H extraTypes extras gamma)))).relabel j)))
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename]
  have h0' := renameInto h0 j Delta hj
  simp only [stepPairRename,numeralRename] at h0'
  have h1' := renameInto h1 j Delta hj
  simp only [stepNumberedPayloadRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [programRename,singletonVectorRename] at h2'
  have h3' := renameInto h3 j Delta hj
  simp only [stepArrowFieldsRename] at h3'
  exact numberedAt H state work request (raw.relabel j) (payload.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j) (base.relabel j) (extraTypes.relabel j) (extras.relabel j) (headData.relabel j) (headResult.relabel j) (baseTypes.relabel j) (typ.relabel j) (gamma.relabel j) hs hc hr h0' h1' h2' h3'

theorem actualOriginalTypedInternalNumberedAcceptance :
    OriginalTypedDecoderInternalAcceptanceTargets.ActualOriginalTypedInternalNumberedAcceptance := by
  intro body H alpha raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma
  let A := StepPair raw (numeral 5) payload ⊓ (StepNumberedPayload payload label head recorded base extraTypes extras ⊓ (programGraph H headData ![head] ⊓ (StepArrowFields headData headResult baseTypes)))
  have hh : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := numberedIff H raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma
    (andLeft (hh)) (andLeft (andRight (hh))) (andLeft (andRight (andRight (hh)))) (andRight (andRight (andRight (hh))))
  exact ⟨Derivation.implicationIntroduction h⟩

theorem consForwardAt (H : Program 1) (state work request raw payload domain head tail typ requestedDomain tailTypes gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 7) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain head tail)))
    (h2 : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain tailTypes)))
    (ha : Nonempty (Derivation body Gamma (ArgumentsAccepted H typ raw gamma))) :
    Nonempty (Derivation body Gamma ((equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H domain head gamma ⊓ (ArgumentsAccepted H tailTypes tail gamma))))) := by
  apply outputCases H 1 state work request gamma typ raw _ hs hc hr ha
  intro beta j Delta out hj ht haccepted
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename]
  have hs' := renameInto hs j Delta hj
  rw [stepLiveRename] at hs'
  have hc' := renameInto hc j Delta hj
  simp only [stepConsRename,zRelabel] at hc'
  have hr' := renameInto hr j Delta hj
  simp only [stepRequestRename,numeralRename] at hr'
  have h0' := renameInto h0 j Delta hj
  simp only [stepPairRename,numeralRename] at h0'
  have h1' := renameInto h1 j Delta hj
  simp only [stepBinaryPayloadRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [stepArrowFieldsRename] at h2'
  have hv := requestValues (state.relabel j) (work.relabel j) (request.relabel j) z
    (numeral 1) (gamma.relabel j) (typ.relabel j) (raw.relabel j) (numeral 7)
    (payload.relabel j) hs' hc' hr' h0'
  have hlocal := argumentsProgramForward H 7 (state.relabel j) (work.relabel j) (request.relabel j) z
    out (gamma.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) hs' hc' hr' h0' ht
  have hg := consGuardAt (state.relabel j) out (gamma.relabel j) (typ.relabel j) (payload.relabel j) (domain.relabel j) (head.relabel j) (tail.relabel j) (requestedDomain.relabel j) (tailTypes.relabel j) z (hv 1) (hv 2) (hv 4) (hv 5) h1' h2' hlocal
  have hgood := acceptedGuard H out (typ.relabel j) (requestedDomain.relabel j) (domain.relabel j) _ hg haccepted
  have hchild := pushTwoAccepted H 0 1 out (gamma.relabel j) (domain.relabel j) (head.relabel j) (gamma.relabel j) (tailTypes.relabel j) (tail.relabel j) (andRight (andRight hgood)) haccepted
  exact andIntro (andLeft hgood) (andIntro (andLeft (andRight hgood)) hchild)

theorem consBackwardAt (H : Program 1) (state work request raw payload domain head tail typ requestedDomain tailTypes gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 7) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain head tail)))
    (h2 : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain tailTypes)))
    (hq : Nonempty (Derivation body Gamma ((equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H domain head gamma ⊓ (ArgumentsAccepted H tailTypes tail gamma)))))) :
    Nonempty (Derivation body Gamma (ArgumentsAccepted H typ raw gamma)) := by
  apply acceptedPushTwoCases H 0 1 gamma domain head gamma tailTypes tail _
    (andLeft (andRight (andRight hq))) (andRight (andRight (andRight hq)))
  intro beta j Delta out hj hpush haccepted
  rw [argumentsAcceptedRename]
  have hs' := renameInto hs j Delta hj
  rw [stepLiveRename] at hs'
  have hc' := renameInto hc j Delta hj
  simp only [stepConsRename,zRelabel] at hc'
  have hr' := renameInto hr j Delta hj
  simp only [stepRequestRename,numeralRename] at hr'
  have h0' := renameInto h0 j Delta hj
  simp only [stepPairRename,numeralRename] at h0'
  have h1' := renameInto h1 j Delta hj
  simp only [stepBinaryPayloadRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [stepArrowFieldsRename] at h2'
  have hq' := renameInto hq j Delta hj
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename] at hq'
  have hguard : Nonempty (Derivation body Delta
      (((equal (typ.relabel j) z).not ⊓ (equal (requestedDomain.relabel j) (domain.relabel j) ⊓
        StepPushTwo out (numeral 0) (gamma.relabel j) (domain.relabel j) (head.relabel j) (numeral 1) (gamma.relabel j) (tailTypes.relabel j) (tail.relabel j) z)) ⊔
        ((equal (typ.relabel j) z ⊔ (equal (requestedDomain.relabel j) (domain.relabel j)).not) ⊓ equal out z))) := by
    obtain ⟨h⟩ := andIntro (andLeft hq') (andIntro (andLeft (andRight hq')) hpush)
    exact ⟨InternalQuotientComparisonProof.orLeft h⟩
  have hbranch := stepArgumentsConsIntro out (gamma.relabel j) (typ.relabel j) (payload.relabel j) z
    (![ (domain.relabel j),(head.relabel j),(tail.relabel j),(requestedDomain.relabel j),(tailTypes.relabel j) ] : Fin 5 → OTerm beta)
    (andIntro h1' (andIntro h2' (hguard)))
  exact argumentsBranchIntro H 7 (state.relabel j) (work.relabel j) (request.relabel j) out
    (gamma.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) hs' hc' hr' h0' hbranch haccepted

theorem consAt (H : Program 1) (state work request raw payload domain head tail typ requestedDomain tailTypes gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 7) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain head tail)))
    (h2 : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain tailTypes))) :
    Nonempty (Derivation body Gamma ((ArgumentsAccepted H typ raw gamma).iff ((equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H domain head gamma ⊓ (ArgumentsAccepted H tailTypes tail gamma)))))) := by
  let P := ArgumentsAccepted H typ raw gamma
  let Q := (equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H domain head gamma ⊓ (ArgumentsAccepted H tailTypes tail gamma)))
  obtain ⟨hf⟩ := consForwardAt H state work request raw payload domain head tail typ requestedDomain tailTypes gamma
    (withHyp hs P) (withHyp hc P) (withHyp hr P) (withHyp h0 P) (withHyp h1 P) (withHyp h2 P)
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := consBackwardAt H state work request raw payload domain head tail typ requestedDomain tailTypes gamma
    (withHyp hs Q) (withHyp hc Q) (withHyp hr Q) (withHyp h0 Q) (withHyp h1 Q) (withHyp h2 Q)
    (show Nonempty (Derivation body (Q :: Gamma) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem consIff (H : Program 1) (raw payload domain head tail typ requestedDomain tailTypes gamma : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 7) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain head tail)))
    (h2 : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain tailTypes))) :
    Nonempty (Derivation body Gamma ((ArgumentsAccepted H typ raw gamma).iff ((equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H domain head gamma ⊓ (ArgumentsAccepted H tailTypes tail gamma)))))) := by
  apply singletonCases 1 typ raw gamma _
  intro beta j Delta state work request hj hs hc hr
  change Nonempty (Derivation body Delta
    (((ArgumentsAccepted H typ raw gamma).relabel j).iff (((equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H domain head gamma ⊓ (ArgumentsAccepted H tailTypes tail gamma)))).relabel j)))
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename]
  have h0' := renameInto h0 j Delta hj
  simp only [stepPairRename,numeralRename] at h0'
  have h1' := renameInto h1 j Delta hj
  simp only [stepBinaryPayloadRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [stepArrowFieldsRename] at h2'
  exact consAt H state work request (raw.relabel j) (payload.relabel j) (domain.relabel j) (head.relabel j) (tail.relabel j) (typ.relabel j) (requestedDomain.relabel j) (tailTypes.relabel j) (gamma.relabel j) hs hc hr h0' h1' h2'

theorem actualOriginalTypedInternalConsAcceptance :
    OriginalTypedDecoderInternalAcceptanceTargets.ActualOriginalTypedInternalConsAcceptance := by
  intro body H alpha raw payload domain head tail typ requestedDomain tailTypes gamma
  let A := StepPair raw (numeral 7) payload ⊓ (StepBinaryPayload payload domain head tail ⊓ (StepArrowFields typ requestedDomain tailTypes))
  have hh : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := consIff H raw payload domain head tail typ requestedDomain tailTypes gamma
    (andLeft (hh)) (andLeft (andRight (hh))) (andRight (andRight (hh)))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBinaryProof
