module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypeSpineProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Induction
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)

open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof

theorem nonzeroFields (types requested tailTypes : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (eqn types z).not))
    (ht : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode types requested tailTypes)) := by
  apply stepArrowFieldsCases types requested tailTypes _ ht
  intro beta j Theta previous hj hp hpair
  rw [graph2Rename]
  have hnj := renameInto hn j Theta hj
  rw [InternalListCodecDecompositionSupportProof.nonzeroRename] at hnj
  have he := InternalListCodecDecompositionSupportProof.predecessorAtNonzero (types.relabel j) previous hnj hp
  exact outputTransport InternalListCodec.consCode (suc previous) (types.relabel j)
    ![requested.relabel j,tailTypes.relabel j] ⟨symm (Classical.choice he)⟩
    (InternalListCodecSupportProof.consValue previous (requested.relabel j) (tailTypes.relabel j) hpair)

theorem matched (types requested domain tailTypes : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode types requested tailTypes)))
    (he : Nonempty (Derivation body Delta (eqn requested domain))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode types domain tailTypes)) := by
  unfold graph2 programGraph at hc ⊢
  apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta
    (OrdinaryArithmetic.graphFormula InternalListCodec.consCode) types ![requested,tailTypes] ![domain,tailTypes] _ hc
  intro i
  fin_cases i
  · rw [InternalSourceInversionSupportProof.onEquality]; exact he
  · rw [InternalSourceInversionSupportProof.onEquality]; exact ⟨refl tailTypes⟩

theorem atCons (H : Program 1) (M W : Program 2)
    (raw domain head tail types requested tailTypes gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw domain head tail)))
    (ht : Nonempty (Derivation body Delta (StepArrowFields types requested tailTypes)))
    (ha : Nonempty (Derivation body Delta
      (OriginalUniverseDecoderInternalAcceptance.ArgumentsAccepted H M W types raw gamma context))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode types domain tailTypes)) := by
  have hi := OriginalUniverseDecoderTransportBinaryAcceptanceProof.consIff H M W
    raw domain head tail types requested tailTypes gamma context hc ht
  have hf := Derivation.implicationElimination (Classical.choice (andLeft hi)) (Classical.choice ha)
  have hn : Nonempty (Derivation body Delta (equal types z).not) := ⟨Derivation.conjunctionLeft hf⟩
  have he : Nonempty (Derivation body Delta (equal requested domain)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hf)⟩
  rw [InternalControlGraphSupportProof.equalEqn] at hn he
  exact matched types requested domain tailTypes (nonzeroFields types requested tailTypes hn ht) he

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypeSpineProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.TypeSpineProof
