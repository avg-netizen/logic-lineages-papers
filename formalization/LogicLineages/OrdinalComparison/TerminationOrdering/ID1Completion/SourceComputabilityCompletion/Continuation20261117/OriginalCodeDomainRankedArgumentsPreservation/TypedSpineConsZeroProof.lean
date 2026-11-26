module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineConsZeroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (symm sucNeZeroApply refl)
open InternalApplicationStepPeelSupportProof (andLeft)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem sourceImpossible (H : Program 1) (M W : Program 2)
    (raw typ head tail gamma context : OTerm alpha) (psi : Formula alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ head tail)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true z raw gamma context))) :
    Nonempty (Derivation body Delta psi) := by
  have ht := OriginalTypedDecoderInternalScalarSyntaxProof.stepArrowFieldsIntro
    (body := body) (Delta := Delta) z z z z InternalEqualityTestPredecessorProof.predecessorZero
    InternalApplicationValidityStackAppendTransitionProof.pairZero
  have hf := OriginalTypedDecoderTransportLogicalProof.iffForward
    (OriginalUniverseDecoderTransportBinaryAcceptanceProof.consIff H M W raw typ head tail z z z gamma context hc ht) ha
  obtain ⟨hn⟩ := andLeft hf
  rw [equalEqn] at hn
  exact ⟨Derivation.explosion (Derivation.implicationElimination hn (refl z))⟩

theorem lengthImpossible (list entry tail : OTerm alpha) (psi : Formula alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list entry tail)))
    (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length z list))) :
    Nonempty (Derivation body Delta psi) := by
  apply programCases OriginalContextInsertion.length ![tail] _
  intro beta j Theta count hj ht
  have hx : (fun i => (![tail] i).relabel j) = ![tail.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at ht
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have hl' := renameInto hl j Theta hj
  simp only [graph1Rename,zRelabel] at hl'
  obtain ⟨he⟩ := OriginalContextInsertionLengthProof.lengthConsRecover (list.relabel j) (entry.relabel j)
    (tail.relabel j) z count hc' hl' ht
  exact ⟨Derivation.explosion (sucNeZeroApply (symm he))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineConsZeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineConsZeroProof
