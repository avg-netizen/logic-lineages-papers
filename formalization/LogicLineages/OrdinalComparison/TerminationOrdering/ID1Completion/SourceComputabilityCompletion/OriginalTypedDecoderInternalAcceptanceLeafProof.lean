module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceLeafSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel OriginalTypedDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalLogicSyntaxProof
open OriginalTypedDecoderInternalAcceptanceSyntaxProof OriginalTypedDecoderInternalAcceptanceStateProof
open OriginalTypedDecoderInternalAcceptanceRunProof OriginalTypedDecoderInternalAcceptanceBranchCasesProof
open OriginalTypedDecoderInternalAcceptanceCheckerProof OriginalTypedDecoderInternalAcceptanceLeafSupportProof
open OriginalTypedDecoderInternalFuelSupportProof (withHyp)
open OriginalTypedDecoderInternalFuelIterationTerminalProof (successPair)
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem variableForwardAt (H : Program 1) (state work request raw payload typ gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 0) payload)))
    (hh : Nonempty (Derivation body Gamma (TermAccepted H typ raw gamma))) :
    Nonempty (Derivation body Gamma (OriginalVariableDecoder.graph (numeral 1) typ payload gamma)) := by
  apply termBranchCases H 0 state work request gamma typ raw payload _ hs hc hr hp hh
  intro beta j Delta out hj hb ha
  simp only [variableGraphRename,oneRename]
  exact variableStepAccepted H out (gamma.relabel j) (typ.relabel j) (payload.relabel j) z hb ha

theorem variableBackwardAt (H : Program 1) (state work request raw payload typ gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 0) payload)))
    (hq : Nonempty (Derivation body Gamma (OriginalVariableDecoder.graph (numeral 1) typ payload gamma))) :
    Nonempty (Derivation body Gamma (TermAccepted H typ raw gamma)) := by
  exact termBranchIntro H 0 state work request (numeral 2) gamma typ raw payload hs hc hr hp
    (variableStepSuccess gamma typ payload hq) (acceptedSuccess H)

theorem variableAt (H : Program 1) (state work request raw payload typ gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 0) payload))) :
    Nonempty (Derivation body Gamma ((TermAccepted H typ raw gamma).iff (OriginalVariableDecoder.graph (numeral 1) typ payload gamma))) := by
  let P := TermAccepted H typ raw gamma
  let Q := OriginalVariableDecoder.graph (numeral 1) typ payload gamma
  obtain ⟨hf⟩ := variableForwardAt H state work request raw payload typ gamma
    (withHyp hs P) (withHyp hc P) (withHyp hr P) (withHyp hp P)
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := variableBackwardAt H state work request raw payload typ gamma
    (withHyp hs Q) (withHyp hc Q) (withHyp hr Q) (withHyp hp Q)
    (show Nonempty (Derivation body (Q :: Gamma) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem variableIff (H : Program 1) (raw payload typ gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 0) payload))) :
    Nonempty (Derivation body Gamma ((TermAccepted H typ raw gamma).iff (OriginalVariableDecoder.graph (numeral 1) typ payload gamma))) := by
  apply singletonCases 0 typ raw gamma _
  intro beta j Delta state work request hj hs hc hr
  change Nonempty (Derivation body Delta
    (((TermAccepted H typ raw gamma).relabel j).iff ((OriginalVariableDecoder.graph (numeral 1) typ payload gamma).relabel j)))
  simp only [termAcceptedRename,variableGraphRename,oneRename]
  have hp' := renameInto hp j Delta hj
  simp only [stepPairRename,numeralRename] at hp'
  exact variableAt H state work request (raw.relabel j) (payload.relabel j) (typ.relabel j)
    (gamma.relabel j) hs hc hr hp'

theorem actualOriginalTypedInternalVariableAcceptance :
    OriginalTypedDecoderInternalAcceptanceTargets.ActualOriginalTypedInternalVariableAcceptance := by
  intro body H alpha raw payload typ gamma
  let A := StepPair raw (numeral 0) payload
  obtain ⟨h⟩ := variableIff (body := body) (Gamma := [A]) H raw payload typ gamma
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem bottomForwardAt (H : Program 1) (state work request raw payload typ gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 3) payload)))
    (hh : Nonempty (Derivation body Gamma (TermAccepted H typ raw gamma))) :
    Nonempty (Derivation body Gamma (equal payload typ)) := by
  apply termBranchCases H 3 state work request gamma typ raw payload _ hs hc hr hp hh
  intro beta j Delta out hj hb ha
  simp only [equalRename]
  exact guardedPopForward H out z (equal (payload.relabel j) (typ.relabel j)) (equal (payload.relabel j) (typ.relabel j)).not hb ha

theorem bottomBackwardAt (H : Program 1) (state work request raw payload typ gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 3) payload)))
    (hq : Nonempty (Derivation body Gamma (equal payload typ))) :
    Nonempty (Derivation body Gamma (TermAccepted H typ raw gamma)) := by
  exact termBranchIntro H 3 state work request (numeral 2) gamma typ raw payload hs hc hr hp
    (by
      obtain ⟨hh⟩ := andIntro hq successPair
      exact ⟨InternalQuotientComparisonProof.orLeft hh⟩) (acceptedSuccess H)

theorem bottomAt (H : Program 1) (state work request raw payload typ gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 3) payload))) :
    Nonempty (Derivation body Gamma ((TermAccepted H typ raw gamma).iff (equal payload typ))) := by
  let P := TermAccepted H typ raw gamma
  let Q := equal payload typ
  obtain ⟨hf⟩ := bottomForwardAt H state work request raw payload typ gamma
    (withHyp hs P) (withHyp hc P) (withHyp hr P) (withHyp hp P)
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := bottomBackwardAt H state work request raw payload typ gamma
    (withHyp hs Q) (withHyp hc Q) (withHyp hr Q) (withHyp hp Q)
    (show Nonempty (Derivation body (Q :: Gamma) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem bottomIff (H : Program 1) (raw payload typ gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 3) payload))) :
    Nonempty (Derivation body Gamma ((TermAccepted H typ raw gamma).iff (equal payload typ))) := by
  apply singletonCases 0 typ raw gamma _
  intro beta j Delta state work request hj hs hc hr
  change Nonempty (Derivation body Delta
    (((TermAccepted H typ raw gamma).relabel j).iff ((equal payload typ).relabel j)))
  simp only [termAcceptedRename,equalRename]
  have hp' := renameInto hp j Delta hj
  simp only [stepPairRename,numeralRename] at hp'
  exact bottomAt H state work request (raw.relabel j) (payload.relabel j) (typ.relabel j)
    (gamma.relabel j) hs hc hr hp'

theorem actualOriginalTypedInternalBottomAcceptance :
    OriginalTypedDecoderInternalAcceptanceTargets.ActualOriginalTypedInternalBottomAcceptance := by
  intro body H alpha raw payload typ gamma
  let A := StepPair raw (numeral 3) payload
  obtain ⟨h⟩ := bottomIff (body := body) (Gamma := [A]) H raw payload typ gamma
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem nilForwardAt (H : Program 1) (state work request raw payload typ gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 6) payload)))
    (hh : Nonempty (Derivation body Gamma (ArgumentsAccepted H typ raw gamma))) :
    Nonempty (Derivation body Gamma (equal payload (numeral 0) ⊓ equal typ (numeral 0))) := by
  apply argumentsBranchCases H 6 state work request gamma typ raw payload _ hs hc hr hp hh
  intro beta j Delta out hj hb ha
  simp only [conjunctionRename,equalRename,numeralRename]
  exact guardedPopForward H out z (equal (payload.relabel j) (numeral 0) ⊓ equal (typ.relabel j) (numeral 0)) ((equal (payload.relabel j) (numeral 0)).not ⊔ (equal (typ.relabel j) (numeral 0)).not) hb ha

theorem nilBackwardAt (H : Program 1) (state work request raw payload typ gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 6) payload)))
    (hq : Nonempty (Derivation body Gamma (equal payload (numeral 0) ⊓ equal typ (numeral 0)))) :
    Nonempty (Derivation body Gamma (ArgumentsAccepted H typ raw gamma)) := by
  exact argumentsBranchIntro H 6 state work request (numeral 2) gamma typ raw payload hs hc hr hp
    (by
      obtain ⟨hh⟩ := andIntro hq successPair
      exact ⟨InternalQuotientComparisonProof.orLeft hh⟩) (acceptedSuccess H)

theorem nilAt (H : Program 1) (state work request raw payload typ gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) gamma typ raw)))
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 6) payload))) :
    Nonempty (Derivation body Gamma ((ArgumentsAccepted H typ raw gamma).iff (equal payload (numeral 0) ⊓ equal typ (numeral 0)))) := by
  let P := ArgumentsAccepted H typ raw gamma
  let Q := equal payload (numeral 0) ⊓ equal typ (numeral 0)
  obtain ⟨hf⟩ := nilForwardAt H state work request raw payload typ gamma
    (withHyp hs P) (withHyp hc P) (withHyp hr P) (withHyp hp P)
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := nilBackwardAt H state work request raw payload typ gamma
    (withHyp hs Q) (withHyp hc Q) (withHyp hr Q) (withHyp hp Q)
    (show Nonempty (Derivation body (Q :: Gamma) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem nilIff (H : Program 1) (raw payload typ gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair raw (numeral 6) payload))) :
    Nonempty (Derivation body Gamma ((ArgumentsAccepted H typ raw gamma).iff (equal payload (numeral 0) ⊓ equal typ (numeral 0)))) := by
  apply singletonCases 1 typ raw gamma _
  intro beta j Delta state work request hj hs hc hr
  change Nonempty (Derivation body Delta
    (((ArgumentsAccepted H typ raw gamma).relabel j).iff ((equal payload (numeral 0) ⊓ equal typ (numeral 0)).relabel j)))
  simp only [argumentsAcceptedRename,conjunctionRename,equalRename,numeralRename]
  have hp' := renameInto hp j Delta hj
  simp only [stepPairRename,numeralRename] at hp'
  exact nilAt H state work request (raw.relabel j) (payload.relabel j) (typ.relabel j)
    (gamma.relabel j) hs hc hr hp'

theorem actualOriginalTypedInternalNilAcceptance :
    OriginalTypedDecoderInternalAcceptanceTargets.ActualOriginalTypedInternalNilAcceptance := by
  intro body H alpha raw payload typ gamma
  let A := StepPair raw (numeral 6) payload
  obtain ⟨h⟩ := nilIff (body := body) (Gamma := [A]) H raw payload typ gamma
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceLeafProof
