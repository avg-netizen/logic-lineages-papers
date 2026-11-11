module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBranchCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel OriginalUniverseDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalLogicSyntaxProof
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof OriginalUniverseDecoderInternalAcceptanceStateProof
open OriginalUniverseDecoderInternalAcceptanceRunProof OriginalUniverseDecoderInternalAcceptanceBranchCasesProof
open OriginalTypedDecoderInternalAcceptanceCheckerProof OriginalUniverseDecoderInternalAcceptanceLeafSupportProof
open OriginalTypedDecoderInternalFuelSupportProof (withHyp)
open OriginalTypedDecoderInternalFuelIterationTerminalProof (successPair)
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem neutralGuard (M W : Program 2) (i : Nat) (h1 : i ≠ 1) (h4 : i ≠ 4) (h5 : i ≠ 5)
    (request gamma typ raw payload c : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral i) payload)))
    (hm : Nonempty (Derivation body Gamma (graph2 M (numeral 1) typ c))) :
    Nonempty (Derivation body Gamma (graph2 (OriginalUniverseDecoder.guard M W) (numeral 1) request c)) :=
  OriginalUniverseDecoderInternalAcceptanceGuardRootProof.termRootBackward M W request gamma typ raw c hr hm
    (OriginalUniverseDecoderInternalAcceptanceGuardRootProof.neutralExtra M W i h1 h4 h5 request c
      (OriginalUniverseDecoderInternalAcceptanceGuardRootProof.requestTagPayload request
        (numeral 0) gamma typ raw (numeral i) payload c hr hp).1)

theorem variableForwardAt (H : Program 1) (M W : Program 2) (state work request raw payload typ gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 0) payload)))
    (hh : Nonempty (Derivation body Gamma (TermAccepted H M W typ raw gamma c))) :
    Nonempty (Derivation body Gamma (graph2 M (numeral 1) typ c ⊓ OriginalVariableDecoder.graph (numeral 1) typ payload gamma)) := by
  apply termBranchCases H M W 0 state work request gamma typ raw payload c _ hs hc hr hp hh
  intro beta j Delta out hj hg hb ha
  simp only [conjunctionRename,graph2Rename,variableGraphRename,oneRename]
  have hr' := renameInto hr j Delta hj
  simp only [OriginalTypedDecoderInternalRequestSyntaxProof.stepRequestRename,numeralRename] at hr'
  have hroot := OriginalUniverseDecoderInternalAcceptanceGuardRootProof.termRootForward M W
    (request.relabel j) (gamma.relabel j) (typ.relabel j) (raw.relabel j) (c.relabel j) hr' hg
  exact andIntro (andLeft hroot) (variableStepAccepted H M W out (gamma.relabel j) (typ.relabel j) (payload.relabel j) z (c.relabel j) hb ha)

theorem variableBackwardAt (H : Program 1) (M W : Program 2) (state work request raw payload typ gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 0) payload)))
    (hq : Nonempty (Derivation body Gamma (graph2 M (numeral 1) typ c ⊓ OriginalVariableDecoder.graph (numeral 1) typ payload gamma))) :
    Nonempty (Derivation body Gamma (TermAccepted H M W typ raw gamma c)) := by
  exact termBranchIntro H M W 0 state work request (numeral 2) gamma typ raw payload c hs hc hr hp
    (neutralGuard M W 0 (by decide) (by decide) (by decide) request gamma typ raw payload c hr hp (andLeft hq))
    (variableStepSuccess gamma typ payload (andRight hq)) (acceptedSuccess H M W c)

theorem variableAt (H : Program 1) (M W : Program 2) (state work request raw payload typ gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 0) payload))) :
    Nonempty (Derivation body Gamma ((TermAccepted H M W typ raw gamma c).iff (graph2 M (numeral 1) typ c ⊓ OriginalVariableDecoder.graph (numeral 1) typ payload gamma))) := by
  let P := TermAccepted H M W typ raw gamma c
  let Q := graph2 M (numeral 1) typ c ⊓ OriginalVariableDecoder.graph (numeral 1) typ payload gamma
  obtain ⟨hf⟩ := variableForwardAt H M W state work request raw payload typ gamma c
    (withHyp hs P) (withHyp hc P) (withHyp hr P) (withHyp hp P)
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := variableBackwardAt H M W state work request raw payload typ gamma c
    (withHyp hs Q) (withHyp hc Q) (withHyp hr Q) (withHyp hp Q)
    (show Nonempty (Derivation body (Q :: Gamma) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem variableIff (H : Program 1) (M W : Program 2) (raw payload typ gamma c : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 0) payload))) :
    Nonempty (Derivation body Gamma ((TermAccepted H M W typ raw gamma c).iff (graph2 M (numeral 1) typ c ⊓ OriginalVariableDecoder.graph (numeral 1) typ payload gamma))) := by
  apply singletonCases 0 typ raw gamma _
  intro beta j Delta state work request hj hs hc hr
  change Nonempty (Derivation body Delta
    (((TermAccepted H M W typ raw gamma c).relabel j).iff ((graph2 M (numeral 1) typ c ⊓ OriginalVariableDecoder.graph (numeral 1) typ payload gamma).relabel j)))
  simp only [termAcceptedRename,conjunctionRename,graph2Rename,variableGraphRename,oneRename]
  have hp' := renameInto hp j Delta hj
  simp only [stepPairRename,numeralRename] at hp'
  exact variableAt H M W state work request (raw.relabel j) (payload.relabel j) (typ.relabel j)
    (gamma.relabel j) (c.relabel j) hs hc hr hp'

theorem actualOriginalUniverseInternalVariableAcceptance :
    OriginalUniverseDecoderInternalAcceptanceTargets.ActualOriginalUniverseInternalVariableAcceptance := by
  intro body H M W alpha raw payload typ gamma c
  let A := StepPair raw (numeral 0) payload
  obtain ⟨h⟩ := variableIff (body := body) (Gamma := [A]) H M W raw payload typ gamma c
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem bottomForwardAt (H : Program 1) (M W : Program 2) (state work request raw payload typ gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 3) payload)))
    (hh : Nonempty (Derivation body Gamma (TermAccepted H M W typ raw gamma c))) :
    Nonempty (Derivation body Gamma (graph2 M (numeral 1) typ c ⊓ equal payload typ)) := by
  apply termBranchCases H M W 3 state work request gamma typ raw payload c _ hs hc hr hp hh
  intro beta j Delta out hj hg hb ha
  simp only [conjunctionRename,graph2Rename,equalRename,oneRename]
  have hr' := renameInto hr j Delta hj
  simp only [OriginalTypedDecoderInternalRequestSyntaxProof.stepRequestRename,numeralRename] at hr'
  have hroot := OriginalUniverseDecoderInternalAcceptanceGuardRootProof.termRootForward M W
    (request.relabel j) (gamma.relabel j) (typ.relabel j) (raw.relabel j) (c.relabel j) hr' hg
  exact andIntro (andLeft hroot) (guardedPopForward H M W out z (c.relabel j) (equal (payload.relabel j) (typ.relabel j)) (equal (payload.relabel j) (typ.relabel j)).not hb ha)

theorem bottomBackwardAt (H : Program 1) (M W : Program 2) (state work request raw payload typ gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 3) payload)))
    (hq : Nonempty (Derivation body Gamma (graph2 M (numeral 1) typ c ⊓ equal payload typ))) :
    Nonempty (Derivation body Gamma (TermAccepted H M W typ raw gamma c)) := by
  exact termBranchIntro H M W 3 state work request (numeral 2) gamma typ raw payload c hs hc hr hp
    (neutralGuard M W 3 (by decide) (by decide) (by decide) request gamma typ raw payload c hr hp (andLeft hq))
    (by
      obtain ⟨hh⟩ := andIntro (andRight hq) successPair
      exact ⟨InternalQuotientComparisonProof.orLeft hh⟩) (acceptedSuccess H M W c)

theorem bottomAt (H : Program 1) (M W : Program 2) (state work request raw payload typ gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 3) payload))) :
    Nonempty (Derivation body Gamma ((TermAccepted H M W typ raw gamma c).iff (graph2 M (numeral 1) typ c ⊓ equal payload typ))) := by
  let P := TermAccepted H M W typ raw gamma c
  let Q := graph2 M (numeral 1) typ c ⊓ equal payload typ
  obtain ⟨hf⟩ := bottomForwardAt H M W state work request raw payload typ gamma c
    (withHyp hs P) (withHyp hc P) (withHyp hr P) (withHyp hp P)
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := bottomBackwardAt H M W state work request raw payload typ gamma c
    (withHyp hs Q) (withHyp hc Q) (withHyp hr Q) (withHyp hp Q)
    (show Nonempty (Derivation body (Q :: Gamma) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem bottomIff (H : Program 1) (M W : Program 2) (raw payload typ gamma c : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 3) payload))) :
    Nonempty (Derivation body Gamma ((TermAccepted H M W typ raw gamma c).iff (graph2 M (numeral 1) typ c ⊓ equal payload typ))) := by
  apply singletonCases 0 typ raw gamma _
  intro beta j Delta state work request hj hs hc hr
  change Nonempty (Derivation body Delta
    (((TermAccepted H M W typ raw gamma c).relabel j).iff ((graph2 M (numeral 1) typ c ⊓ equal payload typ).relabel j)))
  simp only [termAcceptedRename,conjunctionRename,graph2Rename,equalRename,oneRename]
  have hp' := renameInto hp j Delta hj
  simp only [stepPairRename,numeralRename] at hp'
  exact bottomAt H M W state work request (raw.relabel j) (payload.relabel j) (typ.relabel j)
    (gamma.relabel j) (c.relabel j) hs hc hr hp'

theorem actualOriginalUniverseInternalBottomAcceptance :
    OriginalUniverseDecoderInternalAcceptanceTargets.ActualOriginalUniverseInternalBottomAcceptance := by
  intro body H M W alpha raw payload typ gamma c
  let A := StepPair raw (numeral 3) payload
  obtain ⟨h⟩ := bottomIff (body := body) (Gamma := [A]) H M W raw payload typ gamma c
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem nilForwardAt (H : Program 1) (M W : Program 2) (state work request raw payload typ gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 6) payload)))
    (hh : Nonempty (Derivation body Gamma (ArgumentsAccepted H M W typ raw gamma c))) :
    Nonempty (Derivation body Gamma (equal payload (numeral 0) ⊓ equal typ (numeral 0))) := by
  apply argumentsBranchCases H M W 6 state work request gamma typ raw payload c _ hs hc hr hp hh
  intro beta j Delta out hj hb ha
  simp only [conjunctionRename,equalRename,numeralRename]
  exact guardedPopForward H M W out z (c.relabel j) (equal (payload.relabel j) (numeral 0) ⊓ equal (typ.relabel j) (numeral 0)) ((equal (payload.relabel j) (numeral 0)).not ⊔ (equal (typ.relabel j) (numeral 0)).not) hb ha

theorem nilBackwardAt (H : Program 1) (M W : Program 2) (state work request raw payload typ gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 6) payload)))
    (hq : Nonempty (Derivation body Gamma (equal payload (numeral 0) ⊓ equal typ (numeral 0)))) :
    Nonempty (Derivation body Gamma (ArgumentsAccepted H M W typ raw gamma c)) := by
  exact argumentsBranchIntro H M W 6 state work request (numeral 2) gamma typ raw payload c hs hc hr hp
    (by
      obtain ⟨hh⟩ := andIntro hq successPair
      exact ⟨InternalQuotientComparisonProof.orLeft hh⟩) (acceptedSuccess H M W c)

theorem nilAt (H : Program 1) (M W : Program 2) (state work request raw payload typ gamma c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 6) payload))) :
    Nonempty (Derivation body Gamma ((ArgumentsAccepted H M W typ raw gamma c).iff (equal payload (numeral 0) ⊓ equal typ (numeral 0)))) := by
  let P := ArgumentsAccepted H M W typ raw gamma c
  let Q := equal payload (numeral 0) ⊓ equal typ (numeral 0)
  obtain ⟨hf⟩ := nilForwardAt H M W state work request raw payload typ gamma c
    (withHyp hs P) (withHyp hc P) (withHyp hr P) (withHyp hp P)
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := nilBackwardAt H M W state work request raw payload typ gamma c
    (withHyp hs Q) (withHyp hc Q) (withHyp hr Q) (withHyp hp Q)
    (show Nonempty (Derivation body (Q :: Gamma) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem nilIff (H : Program 1) (M W : Program 2) (raw payload typ gamma c : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 6) payload))) :
    Nonempty (Derivation body Gamma ((ArgumentsAccepted H M W typ raw gamma c).iff (equal payload (numeral 0) ⊓ equal typ (numeral 0)))) := by
  apply singletonCases 1 typ raw gamma _
  intro beta j Delta state work request hj hs hc hr
  change Nonempty (Derivation body Delta
    (((ArgumentsAccepted H M W typ raw gamma c).relabel j).iff ((equal payload (numeral 0) ⊓ equal typ (numeral 0)).relabel j)))
  simp only [argumentsAcceptedRename,conjunctionRename,equalRename,numeralRename]
  have hp' := renameInto hp j Delta hj
  simp only [stepPairRename,numeralRename] at hp'
  exact nilAt H M W state work request (raw.relabel j) (payload.relabel j) (typ.relabel j)
    (gamma.relabel j) (c.relabel j) hs hc hr hp'

theorem actualOriginalUniverseInternalNilAcceptance :
    OriginalUniverseDecoderInternalAcceptanceTargets.ActualOriginalUniverseInternalNilAcceptance := by
  intro body H M W alpha raw payload typ gamma c
  let A := StepPair raw (numeral 6) payload
  obtain ⟨h⟩ := nilIff (body := body) (Gamma := [A]) H M W raw payload typ gamma c
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceLeafProof
