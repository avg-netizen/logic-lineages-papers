module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBranchCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalUniverseDecoder OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel
open OriginalUniverseDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalRequestSyntaxProof
open OriginalUniverseDecoderInternalFuelSingletonSupportProof
open OriginalUniverseDecoderInternalFuelSingletonProof
open OriginalUniverseDecoderInternalFuelIterationSyntaxProof
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof
open OriginalUniverseDecoderInternalAcceptancePaidStepProof OriginalUniverseDecoderInternalAcceptanceBranchProof
open OriginalTypedDecoderInternalDispatchSpecificationProof
open OriginalTypedDecoderInternalDispatchSyntaxProof OriginalTypedDecoderInternalLogicSyntaxProof
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem termBranchCases (H : Program 1) (M W : Program 2) (i : Fin 8)
    (state work request g t r p c : OTerm alpha) (psi : Formula alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) g t r)))
    (hp : Nonempty (Derivation body Gamma (StepPair r (numeral i.val) p)))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H M W t r g c)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (out : OTerm beta),
      (∀ q ∈ Gamma, q.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (graph2 (OriginalUniverseDecoder.guard M W) (numeral 1) (request.relabel j) (c.relabel j))) →
      Nonempty (Derivation body Delta
        (termBranchSpec H out (g.relabel j) (t.relabel j) (p.relabel j) z i)) →
      Nonempty (Derivation body Delta (AcceptedState H M W out (c.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  have hw := checkToSingleton H M W 0 state work request g t r c hs hc hr ha
  apply programCases (transition H M W) (Fin.cons state (Fin.cons c Fin.elim0)) _
  intro beta j Delta out hj ht
  simp only [consTermRename,emptyRename] at ht
  have hs' := renameInto hs j Delta hj
  rw [stepLiveRename] at hs'
  have hc' := renameInto hc j Delta hj
  simp only [stepConsRename,zRelabel] at hc'
  have hr' := renameInto hr j Delta hj
  simp only [stepRequestRename,numeralRename] at hr'
  have hp' := renameInto hp j Delta hj
  simp only [stepPairRename,numeralRename] at hp'
  have hw' := renameInto hw j Delta hj
  rw [workAcceptedRename] at hw'
  have haOut := acceptedStepForward H M W (state.relabel j) (work.relabel j) out (c.relabel j) hs' ht hw'
  have htTyped := acceptedTypedTransition H M W (state.relabel j) out (c.relabel j) ht haOut
  exact step beta j Delta out hj
    (acceptedRequestGuard H M W (state.relabel j) (work.relabel j) (request.relabel j) z out (c.relabel j) hs' hc' ht haOut)
    (OriginalTypedDecoderInternalAcceptanceBranchProof.termAtForward H i (state.relabel j) (work.relabel j) (request.relabel j) z
      out (g.relabel j) (t.relabel j) (r.relabel j) (p.relabel j) hs' hc' hr' hp' htTyped)
    haOut

theorem argumentsBranchCases (H : Program 1) (M W : Program 2) (i : Fin 8)
    (state work request g t r p c : OTerm alpha) (psi : Formula alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) g t r)))
    (hp : Nonempty (Derivation body Gamma (StepPair r (numeral i.val) p)))
    (ha : Nonempty (Derivation body Gamma (ArgumentsAccepted H M W t r g c)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (out : OTerm beta),
      (∀ q ∈ Gamma, q.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (argumentsBranchSpec out (g.relabel j) (t.relabel j) (p.relabel j) z i)) →
      Nonempty (Derivation body Delta (AcceptedState H M W out (c.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  have hw := checkToSingleton H M W 1 state work request g t r c hs hc hr ha
  apply programCases (transition H M W) (Fin.cons state (Fin.cons c Fin.elim0)) _
  intro beta j Delta out hj ht
  simp only [consTermRename,emptyRename] at ht
  have hs' := renameInto hs j Delta hj
  rw [stepLiveRename] at hs'
  have hc' := renameInto hc j Delta hj
  simp only [stepConsRename,zRelabel] at hc'
  have hr' := renameInto hr j Delta hj
  simp only [stepRequestRename,numeralRename] at hr'
  have hp' := renameInto hp j Delta hj
  simp only [stepPairRename,numeralRename] at hp'
  have hw' := renameInto hw j Delta hj
  rw [workAcceptedRename] at hw'
  have haOut := acceptedStepForward H M W (state.relabel j) (work.relabel j) out (c.relabel j) hs' ht hw'
  have htTyped := acceptedTypedTransition H M W (state.relabel j) out (c.relabel j) ht haOut
  exact step beta j Delta out hj
    (OriginalTypedDecoderInternalAcceptanceBranchProof.argumentsAtForward H i (state.relabel j) (work.relabel j) (request.relabel j) z
      out (g.relabel j) (t.relabel j) (r.relabel j) (p.relabel j) hs' hc' hr' hp' htTyped)
    haOut

theorem termBranchIntro (H : Program 1) (M W : Program 2) (i : Fin 8)
    (state work request out g t r p c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) g t r)))
    (hp : Nonempty (Derivation body Gamma (StepPair r (numeral i.val) p)))
    (hg : Nonempty (Derivation body Gamma (graph2 (OriginalUniverseDecoder.guard M W) (numeral 1) request c)))
    (hb : Nonempty (Derivation body Gamma (termBranchSpec H out g t p z i)))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H M W out c))) :
    Nonempty (Derivation body Gamma (TermAccepted H M W t r g c)) :=
  singletonToCheck H M W 0 state work request g t r c hs hc hr
    (acceptedStepBackward H M W state work out c hs
      (guardedTransition H M W state work request z out c hs hc hg
        (OriginalTypedDecoderInternalAcceptanceBranchProof.termAtBackward H i state work request z out g t r p hs hc hr hp hb)) ha)

theorem argumentsBranchIntro (H : Program 1) (M W : Program 2) (i : Fin 8)
    (state work request out g t r p c : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) g t r)))
    (hp : Nonempty (Derivation body Gamma (StepPair r (numeral i.val) p)))
    (hb : Nonempty (Derivation body Gamma (argumentsBranchSpec out g t p z i)))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H M W out c))) :
    Nonempty (Derivation body Gamma (ArgumentsAccepted H M W t r g c)) :=
  singletonToCheck H M W 1 state work request g t r c hs hc hr
    (acceptedStepBackward H M W state work out c hs
      (guardedTransition H M W state work request z out c hs hc
        (OriginalUniverseDecoderInternalAcceptanceGuardRootProof.argumentsGuard M W request g t r c hr)
        (OriginalTypedDecoderInternalAcceptanceBranchProof.argumentsAtBackward H i state work request z out g t r p hs hc hr hp hb)) ha)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBranchCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBranchCasesProof
