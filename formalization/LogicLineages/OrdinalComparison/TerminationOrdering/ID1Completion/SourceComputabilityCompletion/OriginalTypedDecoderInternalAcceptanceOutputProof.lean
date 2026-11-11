module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBranchCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceOutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalTypedDecoderInternalFuelSingletonSupportProof
open OriginalTypedDecoderInternalFuelIterationSyntaxProof
open OriginalTypedDecoderInternalAcceptanceStepProof OriginalTypedDecoderInternalAcceptanceBranchProof
open OriginalTypedDecoderInternalTagBranchProof OriginalTypedDecoderInternalModeProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof (branchNumeralElim)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem outputCases (H : Program 1) (mode : Nat)
    (state work request gamma typ raw : OTerm alpha) (psi : Formula alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral mode) gamma typ raw)))
    (ha : Nonempty (Derivation body Gamma (programGraph (checkFor H mode) (numeral 1) ![typ,raw,gamma])))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (out : OTerm beta),
      (∀ q ∈ Gamma, q.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph1 (transition H) out (state.relabel j))) →
      Nonempty (Derivation body Delta (AcceptedState H out)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  have hw := checkToSingleton H mode state work request gamma typ raw hs hc hr ha
  apply programCases (transition H) (Fin.cons state Fin.elim0) _
  intro beta j Delta out hj ht
  simp only [consTermRename,emptyRename] at ht
  have hs' := renameInto hs j Delta hj
  rw [stepLiveRename] at hs'
  have hw' := renameInto hw j Delta hj
  rw [workAcceptedRename] at hw'
  exact step beta j Delta out hj ht
    (acceptedStepForward H (state.relabel j) (work.relabel j) out hs' ht hw')

theorem termProgramForward (H : Program 1) (i : Fin 8)
    (state workCode request suffix out g t r p : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state workCode)))
    (hc : Nonempty (Derivation body Gamma (StepCons workCode request suffix)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 0) g t r)))
    (hp : Nonempty (Derivation body Gamma (StepPair r (numeral i.val) p)))
    (ho : Nonempty (Derivation body Gamma (graph1 (transition H) out state))) :
    Nonempty (Derivation body Gamma (graph1 (termCase H i) out state)) := by
  have hv := requestValues state workCode request suffix (numeral 0) g t r (numeral i.val) p hs hc hr hp
  have hm := modeAtForward H state workCode request suffix out hs hc ho
  have hd := branchNumeralElim 0 0 OriginalTypedDecoder.mode _ (termDispatch H)
    out (Fin.cons state Fin.elim0) (hv 0) hm
  exact termKnownForward H state out i (hv 3) hd

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceOutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceOutputProof
