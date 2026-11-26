module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBranchCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceOutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceOutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalUniverseDecoder OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel
open OriginalUniverseDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalUniverseDecoderInternalFuelSingletonSupportProof
open OriginalUniverseDecoderInternalFuelIterationSyntaxProof
open OriginalUniverseDecoderInternalAcceptancePaidStepProof OriginalUniverseDecoderInternalAcceptanceBranchProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Internally paid guarded output, its actual typed transition, and its
SAME first-request guard. No constructor or successful child is presupposed. -/
theorem outputCases (H : Program 1) (M W : Program 2) (mode : Nat)
    (state work request gamma typ raw c : OTerm alpha) (psi : Formula alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state work)))
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral mode) gamma typ raw)))
    (ha : Nonempty (Derivation body Gamma (programGraph (checkFor H M W mode) (numeral 1) ![typ,raw,gamma,c])))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (out : OTerm beta),
      (∀ q ∈ Gamma, q.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 (guard M W) (numeral 1) (request.relabel j) (c.relabel j))) →
      Nonempty (Derivation body Delta (graph1 (OriginalTypedDecoder.transition H) out (state.relabel j))) →
      Nonempty (Derivation body Delta (AcceptedState H M W out (c.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  have hw := checkToSingleton H M W mode state work request gamma typ raw c hs hc hr ha
  apply programCases (transition H M W) (Fin.cons state (Fin.cons c Fin.elim0)) _
  intro beta j Delta out hj ht
  simp only [consTermRename,emptyRename] at ht
  have hs' := renameInto hs j Delta hj
  rw [stepLiveRename] at hs'
  have hc' := renameInto hc j Delta hj
  simp only [OriginalTypedDecoderInternalScalarSyntaxProof.stepConsRename,zRelabel] at hc'
  have hw' := renameInto hw j Delta hj
  rw [workAcceptedRename] at hw'
  have haccepted := acceptedStepForward H M W (state.relabel j) (work.relabel j) out (c.relabel j) hs' ht hw'
  exact step beta j Delta out hj
    (acceptedRequestGuard H M W (state.relabel j) (work.relabel j) (request.relabel j) z out (c.relabel j) hs' hc' ht haccepted)
    (acceptedTypedTransition H M W (state.relabel j) out (c.relabel j) ht haccepted) haccepted

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceOutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceOutputProof
