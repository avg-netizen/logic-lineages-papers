module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceUnaryLocalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceUnaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel OriginalTypedDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalLogicSyntaxProof
open OriginalTypedDecoderInternalRequestSyntaxProof
open OriginalTypedDecoderInternalAcceptanceSyntaxProof OriginalTypedDecoderInternalAcceptanceStateProof
open OriginalTypedDecoderInternalAcceptanceRunProof OriginalTypedDecoderInternalAcceptanceBranchCasesProof
open OriginalTypedDecoderInternalAcceptanceBranchProof OriginalTypedDecoderInternalAcceptanceCheckerProof
open OriginalTypedDecoderInternalAcceptanceOutputProof OriginalTypedDecoderInternalAcceptancePushProof
open OriginalTypedDecoderInternalAcceptanceUnaryLocalProof
open OriginalTypedDecoderInternalLambdaSyntaxProof OriginalTypedDecoderInternalOrdinarySyntaxProof
open OriginalTypedDecoderInternalFuelSupportProof (withHyp)
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem notRename {beta : Type} (P : Formula alpha) (j : alpha → beta) :
    (P.not).relabel j = (P.relabel j).not := rfl

theorem singletonVectorRename {beta : Type} (head : OTerm alpha) (j : alpha → beta) :
    (fun i : Fin 1 => (![head] i).relabel j) = ![head.relabel j] := by
  funext i
  exact Fin.cases rfl (fun k => Fin.elim0 k) i

theorem lambdaForwardAt (H : Program 1) (state work request raw payload domain child typ requestedDomain codomain gamma extended : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 1) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepPair payload domain child)))
    (h2 : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain codomain)))
    (h3 : Nonempty (Derivation body Gamma (StepCons extended domain gamma)))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H typ raw gamma))) :
    Nonempty (Derivation body Gamma ((equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H codomain child extended)))) := by
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
  simp only [stepPairRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [stepArrowFieldsRename] at h2'
  have h3' := renameInto h3 j Delta hj
  simp only [stepConsRename] at h3'
  have hv := requestValues (state.relabel j) (work.relabel j) (request.relabel j) z
    (numeral 0) (gamma.relabel j) (typ.relabel j) (raw.relabel j) (numeral 1)
    (payload.relabel j) hs' hc' hr' h0'
  have hlocal := termProgramForward H 1 (state.relabel j) (work.relabel j) (request.relabel j) z
    out (gamma.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) hs' hc' hr' h0' ht
  have hg := lambdaGuardAt (state.relabel j) out (gamma.relabel j) (typ.relabel j) (payload.relabel j) (domain.relabel j) (child.relabel j) (requestedDomain.relabel j) (codomain.relabel j) (extended.relabel j) z (hv 1) (hv 2) (hv 4) (hv 5) h1' h2' h3' hlocal
  have hgood := acceptedGuard H out (typ.relabel j) (requestedDomain.relabel j) (domain.relabel j) _ hg haccepted
  have hchild := pushOneAccepted H 0 out (extended.relabel j) (codomain.relabel j) (child.relabel j) (andRight (andRight hgood)) haccepted
  exact andIntro (andLeft hgood) (andIntro (andLeft (andRight hgood)) hchild)

theorem lambdaBackwardAt (H : Program 1) (state work request raw payload domain child typ requestedDomain codomain gamma extended : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 1) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepPair payload domain child)))
    (h2 : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain codomain)))
    (h3 : Nonempty (Derivation body Gamma (StepCons extended domain gamma)))
    (hq : Nonempty (Derivation body Gamma ((equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H codomain child extended))))) :
    Nonempty (Derivation body Gamma (TermAccepted H typ raw gamma)) := by
  apply acceptedPushOneCases H 0 extended codomain child _ (andRight (andRight hq))
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
  simp only [stepPairRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [stepArrowFieldsRename] at h2'
  have h3' := renameInto h3 j Delta hj
  simp only [stepConsRename] at h3'
  have hq' := renameInto hq j Delta hj
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename] at hq'
  have hguard : Nonempty (Derivation body Delta
      (((equal (typ.relabel j) z).not ⊓ (equal (requestedDomain.relabel j) (domain.relabel j) ⊓
        StepPushOne out (numeral 0) (extended.relabel j) (codomain.relabel j) (child.relabel j) z)) ⊔
        ((equal (typ.relabel j) z ⊔ (equal (requestedDomain.relabel j) (domain.relabel j)).not) ⊓ equal out z))) := by
    obtain ⟨h⟩ := andIntro (andLeft hq') (andIntro (andLeft (andRight hq')) hpush)
    exact ⟨InternalQuotientComparisonProof.orLeft h⟩
  have hbranch := stepLambdaIntro out (gamma.relabel j) (typ.relabel j) (payload.relabel j) z
    (![ (domain.relabel j),(child.relabel j),(requestedDomain.relabel j),(codomain.relabel j),(extended.relabel j) ] : Fin 5 → OTerm beta)
    (andIntro h1' (andIntro h2' (andIntro h3' hguard)))
  exact termBranchIntro H 1 (state.relabel j) (work.relabel j) (request.relabel j) out
    (gamma.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) hs' hc' hr' h0' hbranch haccepted

theorem lambdaAt (H : Program 1) (state work request raw payload domain child typ requestedDomain codomain gamma extended : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 1) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepPair payload domain child)))
    (h2 : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain codomain)))
    (h3 : Nonempty (Derivation body Gamma (StepCons extended domain gamma))) :
    Nonempty (Derivation body Gamma ((TermAccepted H typ raw gamma).iff ((equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H codomain child extended))))) := by
  let P := TermAccepted H typ raw gamma
  let Q := (equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H codomain child extended))
  obtain ⟨hf⟩ := lambdaForwardAt H state work request raw payload domain child typ requestedDomain codomain gamma extended
    (withHyp hs P) (withHyp hc P) (withHyp hr P) (withHyp h0 P) (withHyp h1 P) (withHyp h2 P) (withHyp h3 P)
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := lambdaBackwardAt H state work request raw payload domain child typ requestedDomain codomain gamma extended
    (withHyp hs Q) (withHyp hc Q) (withHyp hr Q) (withHyp h0 Q) (withHyp h1 Q) (withHyp h2 Q) (withHyp h3 Q)
    (show Nonempty (Derivation body (Q :: Gamma) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem lambdaIff (H : Program 1) (raw payload domain child typ requestedDomain codomain gamma extended : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 1) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepPair payload domain child)))
    (h2 : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain codomain)))
    (h3 : Nonempty (Derivation body Gamma (StepCons extended domain gamma))) :
    Nonempty (Derivation body Gamma ((TermAccepted H typ raw gamma).iff ((equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H codomain child extended))))) := by
  apply singletonCases 0 typ raw gamma _
  intro beta j Delta state work request hj hs hc hr
  change Nonempty (Derivation body Delta
    (((TermAccepted H typ raw gamma).relabel j).iff (((equal typ z).not ⊓ (equal requestedDomain domain ⊓ (TermAccepted H codomain child extended))).relabel j)))
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename]
  have h0' := renameInto h0 j Delta hj
  simp only [stepPairRename,numeralRename] at h0'
  have h1' := renameInto h1 j Delta hj
  simp only [stepPairRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [stepArrowFieldsRename] at h2'
  have h3' := renameInto h3 j Delta hj
  simp only [stepConsRename] at h3'
  exact lambdaAt H state work request (raw.relabel j) (payload.relabel j) (domain.relabel j) (child.relabel j) (typ.relabel j) (requestedDomain.relabel j) (codomain.relabel j) (gamma.relabel j) (extended.relabel j) hs hc hr h0' h1' h2' h3'

theorem actualOriginalTypedInternalLambdaAcceptance :
    OriginalTypedDecoderInternalAcceptanceTargets.ActualOriginalTypedInternalLambdaAcceptance := by
  intro body H alpha raw payload domain child typ requestedDomain codomain gamma extended
  let A := StepPair raw (numeral 1) payload ⊓ (StepPair payload domain child ⊓ (StepArrowFields typ requestedDomain codomain ⊓ (StepCons extended domain gamma)))
  have hh : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := lambdaIff H raw payload domain child typ requestedDomain codomain gamma extended
    (andLeft (hh)) (andLeft (andRight (hh))) (andLeft (andRight (andRight (hh)))) (andRight (andRight (andRight (hh))))
  exact ⟨Derivation.implicationIntroduction h⟩

theorem ordinaryForwardAt (H : Program 1) (state work request raw payload head base headData result types typ gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 4) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepPair payload head base)))
    (h2 : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (h3 : Nonempty (Derivation body Gamma (StepArrowFields headData result types)))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H typ raw gamma))) :
    Nonempty (Derivation body Gamma ((equal headData z).not ⊓ (equal result typ ⊓ (ArgumentsAccepted H types base gamma)))) := by
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
  simp only [stepPairRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [programRename,singletonVectorRename] at h2'
  have h3' := renameInto h3 j Delta hj
  simp only [stepArrowFieldsRename] at h3'
  have hv := requestValues (state.relabel j) (work.relabel j) (request.relabel j) z
    (numeral 0) (gamma.relabel j) (typ.relabel j) (raw.relabel j) (numeral 4)
    (payload.relabel j) hs' hc' hr' h0'
  have hlocal := termProgramForward H 4 (state.relabel j) (work.relabel j) (request.relabel j) z
    out (gamma.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) hs' hc' hr' h0' ht
  have hg := ordinaryGuardAt H (state.relabel j) out (gamma.relabel j) (typ.relabel j) (payload.relabel j) (head.relabel j) (base.relabel j) (headData.relabel j) (result.relabel j) (types.relabel j) z (hv 1) (hv 2) (hv 4) (hv 5) h1' h2' h3' hlocal
  have hgood := acceptedGuard H out (headData.relabel j) (result.relabel j) (typ.relabel j) _ hg haccepted
  have hchild := pushOneAccepted H 1 out (gamma.relabel j) (types.relabel j) (base.relabel j) (andRight (andRight hgood)) haccepted
  exact andIntro (andLeft hgood) (andIntro (andLeft (andRight hgood)) hchild)

theorem ordinaryBackwardAt (H : Program 1) (state work request raw payload head base headData result types typ gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 4) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepPair payload head base)))
    (h2 : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (h3 : Nonempty (Derivation body Gamma (StepArrowFields headData result types)))
    (hq : Nonempty (Derivation body Gamma ((equal headData z).not ⊓ (equal result typ ⊓ (ArgumentsAccepted H types base gamma))))) :
    Nonempty (Derivation body Gamma (TermAccepted H typ raw gamma)) := by
  apply acceptedPushOneCases H 1 gamma types base _ (andRight (andRight hq))
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
  simp only [stepPairRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [programRename,singletonVectorRename] at h2'
  have h3' := renameInto h3 j Delta hj
  simp only [stepArrowFieldsRename] at h3'
  have hq' := renameInto hq j Delta hj
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename] at hq'
  have hguard : Nonempty (Derivation body Delta
      (((equal (headData.relabel j) z).not ⊓ (equal (result.relabel j) (typ.relabel j) ⊓
        StepPushOne out (numeral 1) (gamma.relabel j) (types.relabel j) (base.relabel j) z)) ⊔
        ((equal (headData.relabel j) z ⊔ (equal (result.relabel j) (typ.relabel j)).not) ⊓ equal out z))) := by
    obtain ⟨h⟩ := andIntro (andLeft hq') (andIntro (andLeft (andRight hq')) hpush)
    exact ⟨InternalQuotientComparisonProof.orLeft h⟩
  have hbranch := stepOrdinaryIntro H out (gamma.relabel j) (typ.relabel j) (payload.relabel j) z
    (![ (head.relabel j),(base.relabel j),(headData.relabel j),(result.relabel j),(types.relabel j) ] : Fin 5 → OTerm beta)
    (andIntro h1' (andIntro h2' (andIntro h3' hguard)))
  exact termBranchIntro H 4 (state.relabel j) (work.relabel j) (request.relabel j) out
    (gamma.relabel j) (typ.relabel j) (raw.relabel j) (payload.relabel j) hs' hc' hr' h0' hbranch haccepted

theorem ordinaryAt (H : Program 1) (state work request raw payload head base headData result types typ gamma : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) gamma typ raw)))
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 4) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepPair payload head base)))
    (h2 : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (h3 : Nonempty (Derivation body Gamma (StepArrowFields headData result types))) :
    Nonempty (Derivation body Gamma ((TermAccepted H typ raw gamma).iff ((equal headData z).not ⊓ (equal result typ ⊓ (ArgumentsAccepted H types base gamma))))) := by
  let P := TermAccepted H typ raw gamma
  let Q := (equal headData z).not ⊓ (equal result typ ⊓ (ArgumentsAccepted H types base gamma))
  obtain ⟨hf⟩ := ordinaryForwardAt H state work request raw payload head base headData result types typ gamma
    (withHyp hs P) (withHyp hc P) (withHyp hr P) (withHyp h0 P) (withHyp h1 P) (withHyp h2 P) (withHyp h3 P)
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := ordinaryBackwardAt H state work request raw payload head base headData result types typ gamma
    (withHyp hs Q) (withHyp hc Q) (withHyp hr Q) (withHyp h0 Q) (withHyp h1 Q) (withHyp h2 Q) (withHyp h3 Q)
    (show Nonempty (Derivation body (Q :: Gamma) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem ordinaryIff (H : Program 1) (raw payload head base headData result types typ gamma : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 4) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepPair payload head base)))
    (h2 : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (h3 : Nonempty (Derivation body Gamma (StepArrowFields headData result types))) :
    Nonempty (Derivation body Gamma ((TermAccepted H typ raw gamma).iff ((equal headData z).not ⊓ (equal result typ ⊓ (ArgumentsAccepted H types base gamma))))) := by
  apply singletonCases 0 typ raw gamma _
  intro beta j Delta state work request hj hs hc hr
  change Nonempty (Derivation body Delta
    (((TermAccepted H typ raw gamma).relabel j).iff (((equal headData z).not ⊓ (equal result typ ⊓ (ArgumentsAccepted H types base gamma))).relabel j)))
  simp only [conjunctionRename,notRename,equalRename,zRelabel,termAcceptedRename,argumentsAcceptedRename]
  have h0' := renameInto h0 j Delta hj
  simp only [stepPairRename,numeralRename] at h0'
  have h1' := renameInto h1 j Delta hj
  simp only [stepPairRename] at h1'
  have h2' := renameInto h2 j Delta hj
  simp only [programRename,singletonVectorRename] at h2'
  have h3' := renameInto h3 j Delta hj
  simp only [stepArrowFieldsRename] at h3'
  exact ordinaryAt H state work request (raw.relabel j) (payload.relabel j) (head.relabel j) (base.relabel j) (headData.relabel j) (result.relabel j) (types.relabel j) (typ.relabel j) (gamma.relabel j) hs hc hr h0' h1' h2' h3'

theorem actualOriginalTypedInternalOrdinaryAcceptance :
    OriginalTypedDecoderInternalAcceptanceTargets.ActualOriginalTypedInternalOrdinaryAcceptance := by
  intro body H alpha raw payload head base headData result types typ gamma
  let A := StepPair raw (numeral 4) payload ⊓ (StepPair payload head base ⊓ (programGraph H headData ![head] ⊓ (StepArrowFields headData result types)))
  have hh : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := ordinaryIff H raw payload head base headData result types typ gamma
    (andLeft (hh)) (andLeft (andRight (hh))) (andLeft (andRight (andRight (hh)))) (andRight (andRight (andRight (hh))))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceUnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceUnaryProof
