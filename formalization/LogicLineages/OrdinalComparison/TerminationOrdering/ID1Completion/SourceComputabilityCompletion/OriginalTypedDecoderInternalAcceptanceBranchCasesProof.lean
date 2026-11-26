module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCheckerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBranchCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalRequestSyntaxProof
open OriginalTypedDecoderInternalFuelSingletonSupportProof
open OriginalTypedDecoderInternalFuelSingletonProof
open OriginalTypedDecoderInternalFuelIterationSyntaxProof
open OriginalTypedDecoderInternalAcceptanceSyntaxProof
open OriginalTypedDecoderInternalAcceptanceStepProof OriginalTypedDecoderInternalAcceptanceBranchProof
open OriginalTypedDecoderInternalDispatchSpecificationProof
open OriginalTypedDecoderInternalDispatchSyntaxProof OriginalTypedDecoderInternalLogicSyntaxProof
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem termBranchCases (H : Program 1) (i : Fin 8)
    (state work request g t r p : OTerm alpha) (psi : Formula alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) g t r)))
    (hp : Nonempty (Derivation body Gamma (StepPair r (numeral i.val) p)))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H t r g)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (out : OTerm beta),
      (∀ q ∈ Gamma, q.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (termBranchSpec H out (g.relabel j) (t.relabel j) (p.relabel j) z i)) →
      Nonempty (Derivation body Delta (AcceptedState H out)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  have hw := checkToSingleton H 0 state work request g t r hs hc hr ha
  apply programCases (transition H) (Fin.cons state Fin.elim0) _
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
  exact step beta j Delta out hj
    (termAtForward H i (state.relabel j) (work.relabel j) (request.relabel j) z
      out (g.relabel j) (t.relabel j) (r.relabel j) (p.relabel j) hs' hc' hr' hp' ht)
    (acceptedStepForward H (state.relabel j) (work.relabel j) out hs' ht hw')

theorem argumentsBranchCases (H : Program 1) (i : Fin 8)
    (state work request g t r p : OTerm alpha) (psi : Formula alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) g t r)))
    (hp : Nonempty (Derivation body Gamma (StepPair r (numeral i.val) p)))
    (ha : Nonempty (Derivation body Gamma (ArgumentsAccepted H t r g)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (out : OTerm beta),
      (∀ q ∈ Gamma, q.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (argumentsBranchSpec out (g.relabel j) (t.relabel j) (p.relabel j) z i)) →
      Nonempty (Derivation body Delta (AcceptedState H out)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  have hw := checkToSingleton H 1 state work request g t r hs hc hr ha
  apply programCases (transition H) (Fin.cons state Fin.elim0) _
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
  exact step beta j Delta out hj
    (argumentsAtForward H i (state.relabel j) (work.relabel j) (request.relabel j) z
      out (g.relabel j) (t.relabel j) (r.relabel j) (p.relabel j) hs' hc' hr' hp' ht)
    (acceptedStepForward H (state.relabel j) (work.relabel j) out hs' ht hw')

theorem termBranchIntro (H : Program 1) (i : Fin 8)
    (state work request out g t r p : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) g t r)))
    (hp : Nonempty (Derivation body Gamma (StepPair r (numeral i.val) p)))
    (hb : Nonempty (Derivation body Gamma (termBranchSpec H out g t p z i)))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H out))) :
    Nonempty (Derivation body Gamma (TermAccepted H t r g)) :=
  singletonToCheck H 0 state work request g t r hs hc hr
    (acceptedStepBackward H state work out hs
      (termAtBackward H i state work request z out g t r p hs hc hr hp hb) ha)

theorem argumentsBranchIntro (H : Program 1) (i : Fin 8)
    (state work request out g t r p : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) g t r)))
    (hp : Nonempty (Derivation body Gamma (StepPair r (numeral i.val) p)))
    (hb : Nonempty (Derivation body Gamma (argumentsBranchSpec out g t p z i)))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H out))) :
    Nonempty (Derivation body Gamma (ArgumentsAccepted H t r g)) :=
  singletonToCheck H 1 state work request g t r hs hc hr
    (acceptedStepBackward H state work out hs
      (argumentsAtBackward H i state work request z out g t r p hs hc hr hp hb) ha)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBranchCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBranchCasesProof
