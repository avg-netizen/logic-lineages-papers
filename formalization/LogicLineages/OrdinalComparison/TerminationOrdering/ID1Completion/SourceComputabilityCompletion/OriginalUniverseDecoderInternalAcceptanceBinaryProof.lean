module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBinaryLocalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceUnaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel OriginalUniverseDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalLogicSyntaxProof
open OriginalTypedDecoderInternalRequestSyntaxProof OriginalTypedDecoderInternalBinarySyntaxProof
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof OriginalUniverseDecoderInternalAcceptanceStateProof
open OriginalUniverseDecoderInternalAcceptanceBranchCasesProof OriginalTypedDecoderInternalAcceptanceBranchProof
open OriginalTypedDecoderInternalAcceptanceCheckerProof OriginalUniverseDecoderInternalAcceptanceOutputProof
open OriginalUniverseDecoderInternalAcceptancePushTwoProof OriginalTypedDecoderInternalAcceptanceBinaryLocalProof
open OriginalTypedDecoderInternalAcceptanceOutputProof (termProgramForward)
open OriginalUniverseDecoderInternalAcceptanceBinaryLocalProof
open OriginalUniverseDecoderInternalAcceptanceUnaryLocalProof
open OriginalUniverseDecoderInternalAcceptanceLeafProof (neutralGuard)
open OriginalUniverseDecoderInternalAcceptanceGuardRootProof
open OriginalUniverseDecoderInternalAcceptanceGuardNumberedProof
open OriginalTypedDecoderInternalAcceptanceUnaryProof (notRename singletonVectorRename)
open OriginalTypedDecoderInternalApplicationSyntaxProof OriginalTypedDecoderInternalNumberedSyntaxProof
open OriginalTypedDecoderInternalConsSyntaxProof
open OriginalTypedDecoderInternalFuelSupportProof (withHyp)
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem applicationForwardAt (H : Program 1) (M W : Program 2) (state work request raw payload domain fn arg typ arrow gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 2) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain fn arg)))
    (h2 : Nonempty (Derivation body Gamma (StepCons arrow domain typ)))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H M W typ raw gamma c))) :
    Nonempty (Derivation body Gamma (graph2 M (numeral 1) typ c ⊓ (TermAccepted H M W arrow fn gamma c ⊓ (TermAccepted H M W domain arg gamma c)))) := by
  apply outputCases H M W 0 state work request gamma typ raw c _ hs hc hr ha
  intro beta j Delta out hj hsource ht haccepted
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename,graph2Rename,oneRename]
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
  have hchild := pushTwoAccepted H M W 0 0 out (gamma.relabel j) (arrow.relabel j) (fn.relabel j) (gamma.relabel j) (domain.relabel j) (arg.relabel j) (c.relabel j) hg haccepted
  have hroot := termRootForward M W (request.relabel j) (gamma.relabel j)
    (typ.relabel j) (raw.relabel j) (c.relabel j) hr' hsource
  exact andIntro (andLeft hroot) hchild

theorem applicationBackwardAt (H : Program 1) (M W : Program 2) (state work request raw payload domain fn arg typ arrow gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 2) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain fn arg)))
    (h2 : Nonempty (Derivation body Gamma (StepCons arrow domain typ)))
    (hq : Nonempty (Derivation body Gamma (graph2 M (numeral 1) typ c ⊓ (TermAccepted H M W arrow fn gamma c ⊓ (TermAccepted H M W domain arg gamma c))))) :
    Nonempty (Derivation body Gamma (TermAccepted H M W typ raw gamma c)) := by
  apply acceptedPushTwoCases H M W 0 0 gamma arrow fn gamma domain arg c _
    (andLeft (andRight hq)) (andRight (andRight hq))
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
  have hq' := renameInto hq j Delta hj
  simp only [conjunctionRename,graph2Rename,oneRename,termAcceptedRename] at hq'
  have hsource := neutralGuard M W 2 (by decide) (by decide) (by decide)
    (request.relabel j) (gamma.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j)
    (c.relabel j) hr' h0' (andLeft hq')
  have hbranch := stepApplicationIntro out (gamma.relabel j) (typ.relabel j) (payload.relabel j) z
    (![ (domain.relabel j),(fn.relabel j),(arg.relabel j),(arrow.relabel j) ] : Fin 4 → OTerm beta)
    (andIntro h1' (andIntro h2' (hpush)))
  exact termBranchIntro H M W 2 (state.relabel j) (work.relabel j) (request.relabel j) out
    (gamma.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) (c.relabel j) hs' hc' hr' h0' hsource hbranch haccepted

theorem applicationAt (H : Program 1) (M W : Program 2) (state work request raw payload domain fn arg typ arrow gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 2) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain fn arg)))
    (h2 : Nonempty (Derivation body Gamma (StepCons arrow domain typ))) :
    Nonempty (Derivation body Gamma ((TermAccepted H M W typ raw gamma c).iff (graph2 M (numeral 1) typ c ⊓ (TermAccepted H M W arrow fn gamma c ⊓ (TermAccepted H M W domain arg gamma c))))) := by
  let P := TermAccepted H M W typ raw gamma c
  let Q := graph2 M (numeral 1) typ c ⊓ (TermAccepted H M W arrow fn gamma c ⊓ (TermAccepted H M W domain arg gamma c))
  obtain ⟨hf⟩ := applicationForwardAt H M W state work request raw payload domain fn arg typ arrow gamma c
    (withHyp hs P) (withHyp hc P) (withHyp hr P) (withHyp h0 P) (withHyp h1 P) (withHyp h2 P)
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := applicationBackwardAt H M W state work request raw payload domain fn arg typ arrow gamma c
    (withHyp hs Q) (withHyp hc Q) (withHyp hr Q) (withHyp h0 Q) (withHyp h1 Q) (withHyp h2 Q)
    (show Nonempty (Derivation body (Q :: Gamma) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem applicationIff (H : Program 1) (M W : Program 2) (raw payload domain fn arg typ arrow gamma c : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 2) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain fn arg)))
    (h2 : Nonempty (Derivation body Gamma (StepCons arrow domain typ))) :
    Nonempty (Derivation body Gamma ((TermAccepted H M W typ raw gamma c).iff (graph2 M (numeral 1) typ c ⊓ (TermAccepted H M W arrow fn gamma c ⊓ (TermAccepted H M W domain arg gamma c))))) := by
  apply singletonCases 0 typ raw gamma _
  intro beta j Delta state work request hj hs hc hr
  change Nonempty (Derivation body Delta
    (((TermAccepted H M W typ raw gamma c).relabel j).iff ((graph2 M (numeral 1) typ c ⊓ (TermAccepted H M W arrow fn gamma c ⊓ (TermAccepted H M W domain arg gamma c))).relabel j)))
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename,graph2Rename,oneRename]
  have h0' := renameInto h0 j Delta hj
  simp only [stepPairRename,numeralRename] at h0'
  have h1' := renameInto h1 j Delta hj
  simp only [stepBinaryPayloadRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [stepConsRename] at h2'
  exact applicationAt H M W state work request (raw.relabel j) (payload.relabel j) (domain.relabel j) (fn.relabel j) (arg.relabel j) (typ.relabel j) (arrow.relabel j) (gamma.relabel j) (c.relabel j) hs hc hr h0' h1' h2'

theorem actualOriginalUniverseInternalApplicationAcceptance :
    OriginalUniverseDecoderInternalAcceptanceTargets.ActualOriginalUniverseInternalApplicationAcceptance := by
  intro body H M W alpha raw payload domain fn arg typ arrow gamma c
  let A := StepPair raw (numeral 2) payload ⊓ (StepBinaryPayload payload domain fn arg ⊓ (StepCons arrow domain typ))
  have hh : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := applicationIff H M W raw payload domain fn arg typ arrow gamma c
    (andLeft (hh)) (andLeft (andRight (hh))) (andRight (andRight (hh)))
  exact ⟨Derivation.implicationIntroduction h⟩

theorem numberedForwardAt (H : Program 1) (M W : Program 2) (state work request raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 5) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepNumberedPayload payload label head recorded base extraTypes extras)))
    (h2 : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (h3 : Nonempty (Derivation body Gamma (StepArrowFields headData headResult baseTypes)))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H M W typ raw gamma c))) :
    Nonempty (Derivation body Gamma (graph2 M (numeral 1) typ c ⊓ (graph2 W (numeral 1) head c ⊓ ((equal headData z).not ⊓ (equal recorded typ ⊓ (ArgumentsAccepted H M W baseTypes base gamma c ⊓ (ArgumentsAccepted H M W extraTypes extras gamma c))))))) := by
  apply outputCases H M W 0 state work request gamma typ raw c _ hs hc hr ha
  intro beta j Delta out hj hsource ht haccepted
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename,graph2Rename,oneRename]
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
  have hgood := guardedPushTwoAccepted H M W 1 1 out (headData.relabel j) (recorded.relabel j) (typ.relabel j)
    (gamma.relabel j) (baseTypes.relabel j) (base.relabel j) (gamma.relabel j) (extraTypes.relabel j) (extras.relabel j) (c.relabel j) hg haccepted
  have hroot := numberedRootForward M W (request.relabel j) (gamma.relabel j) (typ.relabel j)
    (raw.relabel j) (payload.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j)
    (base.relabel j) (extraTypes.relabel j) (extras.relabel j) (c.relabel j) hr' h0' h1' hsource
  exact andIntro (andLeft hroot) (andIntro (andRight hroot) hgood)

theorem numberedBackwardAt (H : Program 1) (M W : Program 2) (state work request raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 5) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepNumberedPayload payload label head recorded base extraTypes extras)))
    (h2 : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (h3 : Nonempty (Derivation body Gamma (StepArrowFields headData headResult baseTypes)))
    (hq : Nonempty (Derivation body Gamma (graph2 M (numeral 1) typ c ⊓ (graph2 W (numeral 1) head c ⊓ ((equal headData z).not ⊓ (equal recorded typ ⊓ (ArgumentsAccepted H M W baseTypes base gamma c ⊓ (ArgumentsAccepted H M W extraTypes extras gamma c)))))))) :
    Nonempty (Derivation body Gamma (TermAccepted H M W typ raw gamma c)) := by
  apply acceptedPushTwoCases H M W 1 1 gamma baseTypes base gamma extraTypes extras c _
    (andLeft (andRight (andRight (andRight (andRight hq))))) (andRight (andRight (andRight (andRight (andRight hq)))))
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
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename,graph2Rename,oneRename] at hq'
  have hsource := numberedRootBackward M W (request.relabel j) (gamma.relabel j) (typ.relabel j)
    (raw.relabel j) (payload.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j)
    (base.relabel j) (extraTypes.relabel j) (extras.relabel j) (c.relabel j) hr' h0' h1'
    (andLeft hq') (andLeft (andRight hq'))
  have hpure := andRight (andRight hq')
  have hguard : Nonempty (Derivation body Delta
      (((equal (headData.relabel j) z).not ⊓ (equal (recorded.relabel j) (typ.relabel j) ⊓
        StepPushTwo out (numeral 1) (gamma.relabel j) (baseTypes.relabel j) (base.relabel j) (numeral 1) (gamma.relabel j) (extraTypes.relabel j) (extras.relabel j) z)) ⊔
        ((equal (headData.relabel j) z ⊔ (equal (recorded.relabel j) (typ.relabel j)).not) ⊓ equal out z))) := by
    obtain ⟨h⟩ := andIntro (andLeft hpure) (andIntro (andLeft (andRight hpure)) hpush)
    exact ⟨InternalQuotientComparisonProof.orLeft h⟩
  have hbranch := stepNumberedIntro H out (gamma.relabel j) (typ.relabel j) (payload.relabel j) z
    (![ (label.relabel j),(head.relabel j),(recorded.relabel j),(base.relabel j),(extraTypes.relabel j),(extras.relabel j),(headData.relabel j),(headResult.relabel j),(baseTypes.relabel j) ] : Fin 9 → OTerm beta)
    (andIntro h1' (andIntro h2' (andIntro h3' (hguard))))
  exact termBranchIntro H M W 5 (state.relabel j) (work.relabel j) (request.relabel j) out
    (gamma.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) (c.relabel j) hs' hc' hr' h0' hsource hbranch haccepted

theorem numberedAt (H : Program 1) (M W : Program 2) (state work request raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 5) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepNumberedPayload payload label head recorded base extraTypes extras)))
    (h2 : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (h3 : Nonempty (Derivation body Gamma (StepArrowFields headData headResult baseTypes))) :
    Nonempty (Derivation body Gamma ((TermAccepted H M W typ raw gamma c).iff (graph2 M (numeral 1) typ c ⊓ (graph2 W (numeral 1) head c ⊓ ((equal headData z).not ⊓ (equal recorded typ ⊓ (ArgumentsAccepted H M W baseTypes base gamma c ⊓ (ArgumentsAccepted H M W extraTypes extras gamma c)))))))) := by
  let P := TermAccepted H M W typ raw gamma c
  let Q := graph2 M (numeral 1) typ c ⊓ (graph2 W (numeral 1) head c ⊓ ((equal headData z).not ⊓ (equal recorded typ ⊓ (ArgumentsAccepted H M W baseTypes base gamma c ⊓ (ArgumentsAccepted H M W extraTypes extras gamma c)))))
  obtain ⟨hf⟩ := numberedForwardAt H M W state work request raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma c
    (withHyp hs P) (withHyp hc P) (withHyp hr P) (withHyp h0 P) (withHyp h1 P) (withHyp h2 P) (withHyp h3 P)
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := numberedBackwardAt H M W state work request raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma c
    (withHyp hs Q) (withHyp hc Q) (withHyp hr Q) (withHyp h0 Q) (withHyp h1 Q) (withHyp h2 Q) (withHyp h3 Q)
    (show Nonempty (Derivation body (Q :: Gamma) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem numberedIff (H : Program 1) (M W : Program 2) (raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma c : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 5) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepNumberedPayload payload label head recorded base extraTypes extras)))
    (h2 : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (h3 : Nonempty (Derivation body Gamma (StepArrowFields headData headResult baseTypes))) :
    Nonempty (Derivation body Gamma ((TermAccepted H M W typ raw gamma c).iff (graph2 M (numeral 1) typ c ⊓ (graph2 W (numeral 1) head c ⊓ ((equal headData z).not ⊓ (equal recorded typ ⊓ (ArgumentsAccepted H M W baseTypes base gamma c ⊓ (ArgumentsAccepted H M W extraTypes extras gamma c)))))))) := by
  apply singletonCases 0 typ raw gamma _
  intro beta j Delta state work request hj hs hc hr
  change Nonempty (Derivation body Delta
    (((TermAccepted H M W typ raw gamma c).relabel j).iff ((graph2 M (numeral 1) typ c ⊓ (graph2 W (numeral 1) head c ⊓ ((equal headData z).not ⊓ (equal recorded typ ⊓ (ArgumentsAccepted H M W baseTypes base gamma c ⊓ (ArgumentsAccepted H M W extraTypes extras gamma c)))))).relabel j)))
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename,graph2Rename,oneRename]
  have h0' := renameInto h0 j Delta hj
  simp only [stepPairRename,numeralRename] at h0'
  have h1' := renameInto h1 j Delta hj
  simp only [stepNumberedPayloadRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [programRename,singletonVectorRename] at h2'
  have h3' := renameInto h3 j Delta hj
  simp only [stepArrowFieldsRename] at h3'
  exact numberedAt H M W state work request (raw.relabel j) (payload.relabel j) (label.relabel j) (head.relabel j) (recorded.relabel j) (base.relabel j) (extraTypes.relabel j) (extras.relabel j) (headData.relabel j) (headResult.relabel j) (baseTypes.relabel j) (typ.relabel j) (gamma.relabel j) (c.relabel j) hs hc hr h0' h1' h2' h3'

theorem actualOriginalUniverseInternalNumberedAcceptance :
    OriginalUniverseDecoderInternalAcceptanceTargets.ActualOriginalUniverseInternalNumberedAcceptance := by
  intro body H M W alpha raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma c
  let A := StepPair raw (numeral 5) payload ⊓ (StepNumberedPayload payload label head recorded base extraTypes extras ⊓ (programGraph H headData ![head] ⊓ (StepArrowFields headData headResult baseTypes)))
  have hh : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := numberedIff H M W raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma c
    (andLeft (hh)) (andLeft (andRight (hh))) (andLeft (andRight (andRight (hh)))) (andRight (andRight (andRight (hh))))
  exact ⟨Derivation.implicationIntroduction h⟩

theorem consForwardAt (H : Program 1) (M W : Program 2) (state work request raw payload domain head tail typ requestedDomain tailTypes gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 7) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain head tail)))
    (h2 : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain tailTypes)))
    (ha : Nonempty (Derivation body Gamma (ArgumentsAccepted H M W typ raw gamma c))) :
    Nonempty (Derivation body Gamma ((equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H M W domain head gamma c ⊓ (ArgumentsAccepted H M W tailTypes tail gamma c))))) := by
  apply outputCases H M W 1 state work request gamma typ raw c _ hs hc hr ha
  intro beta j Delta out hj hsource ht haccepted
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename,graph2Rename,oneRename]
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
  exact guardedPushTwoAccepted H M W 0 1 out (typ.relabel j) (requestedDomain.relabel j) (domain.relabel j)
    (gamma.relabel j) (domain.relabel j) (head.relabel j) (gamma.relabel j) (tailTypes.relabel j) (tail.relabel j) (c.relabel j) hg haccepted

theorem consBackwardAt (H : Program 1) (M W : Program 2) (state work request raw payload domain head tail typ requestedDomain tailTypes gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 7) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain head tail)))
    (h2 : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain tailTypes)))
    (hq : Nonempty (Derivation body Gamma ((equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H M W domain head gamma c ⊓ (ArgumentsAccepted H M W tailTypes tail gamma c)))))) :
    Nonempty (Derivation body Gamma (ArgumentsAccepted H M W typ raw gamma c)) := by
  apply acceptedPushTwoCases H M W 0 1 gamma domain head gamma tailTypes tail c _
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
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename,graph2Rename,oneRename] at hq'
  have hguard : Nonempty (Derivation body Delta
      (((equal (typ.relabel j) z).not ⊓ (equal (requestedDomain.relabel j) (domain.relabel j) ⊓
        StepPushTwo out (numeral 0) (gamma.relabel j) (domain.relabel j) (head.relabel j) (numeral 1) (gamma.relabel j) (tailTypes.relabel j) (tail.relabel j) z)) ⊔
        ((equal (typ.relabel j) z ⊔ (equal (requestedDomain.relabel j) (domain.relabel j)).not) ⊓ equal out z))) := by
    obtain ⟨h⟩ := andIntro (andLeft hq') (andIntro (andLeft (andRight hq')) hpush)
    exact ⟨InternalQuotientComparisonProof.orLeft h⟩
  have hbranch := stepArgumentsConsIntro out (gamma.relabel j) (typ.relabel j) (payload.relabel j) z
    (![ (domain.relabel j),(head.relabel j),(tail.relabel j),(requestedDomain.relabel j),(tailTypes.relabel j) ] : Fin 5 → OTerm beta)
    (andIntro h1' (andIntro h2' (hguard)))
  exact argumentsBranchIntro H M W 7 (state.relabel j) (work.relabel j) (request.relabel j) out
    (gamma.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) (c.relabel j) hs' hc' hr' h0' hbranch haccepted

theorem consAt (H : Program 1) (M W : Program 2) (state work request raw payload domain head tail typ requestedDomain tailTypes gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 7) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain head tail)))
    (h2 : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain tailTypes))) :
    Nonempty (Derivation body Gamma ((ArgumentsAccepted H M W typ raw gamma c).iff ((equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H M W domain head gamma c ⊓ (ArgumentsAccepted H M W tailTypes tail gamma c)))))) := by
  let P := ArgumentsAccepted H M W typ raw gamma c
  let Q := (equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H M W domain head gamma c ⊓ (ArgumentsAccepted H M W tailTypes tail gamma c)))
  obtain ⟨hf⟩ := consForwardAt H M W state work request raw payload domain head tail typ requestedDomain tailTypes gamma c
    (withHyp hs P) (withHyp hc P) (withHyp hr P) (withHyp h0 P) (withHyp h1 P) (withHyp h2 P)
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := consBackwardAt H M W state work request raw payload domain head tail typ requestedDomain tailTypes gamma c
    (withHyp hs Q) (withHyp hc Q) (withHyp hr Q) (withHyp h0 Q) (withHyp h1 Q) (withHyp h2 Q)
    (show Nonempty (Derivation body (Q :: Gamma) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem consIff (H : Program 1) (M W : Program 2) (raw payload domain head tail typ requestedDomain tailTypes gamma c : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 7) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain head tail)))
    (h2 : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain tailTypes))) :
    Nonempty (Derivation body Gamma ((ArgumentsAccepted H M W typ raw gamma c).iff ((equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H M W domain head gamma c ⊓ (ArgumentsAccepted H M W tailTypes tail gamma c)))))) := by
  apply singletonCases 1 typ raw gamma _
  intro beta j Delta state work request hj hs hc hr
  change Nonempty (Derivation body Delta
    (((ArgumentsAccepted H M W typ raw gamma c).relabel j).iff (((equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H M W domain head gamma c ⊓ (ArgumentsAccepted H M W tailTypes tail gamma c)))).relabel j)))
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename,graph2Rename,oneRename]
  have h0' := renameInto h0 j Delta hj
  simp only [stepPairRename,numeralRename] at h0'
  have h1' := renameInto h1 j Delta hj
  simp only [stepBinaryPayloadRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [stepArrowFieldsRename] at h2'
  exact consAt H M W state work request (raw.relabel j) (payload.relabel j) (domain.relabel j) (head.relabel j) (tail.relabel j) (typ.relabel j) (requestedDomain.relabel j) (tailTypes.relabel j) (gamma.relabel j) (c.relabel j) hs hc hr h0' h1' h2'

theorem actualOriginalUniverseInternalConsAcceptance :
    OriginalUniverseDecoderInternalAcceptanceTargets.ActualOriginalUniverseInternalConsAcceptance := by
  intro body H M W alpha raw payload domain head tail typ requestedDomain tailTypes gamma c
  let A := StepPair raw (numeral 7) payload ⊓ (StepBinaryPayload payload domain head tail ⊓ (StepArrowFields typ requestedDomain tailTypes))
  have hh : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := consIff H M W raw payload domain head tail typ requestedDomain tailTypes gamma c
    (andLeft (hh)) (andLeft (andRight (hh))) (andRight (andRight (hh)))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBinaryProof
