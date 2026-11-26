module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportVariableProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl symm trans congSuc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal OriginalRawVariableRank
open OriginalRawVariableRankTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalRawVariableRankTransportArithmeticProof OriginalRawVariableRankTransportSyntaxProof
open OriginalRawVariableRankLeafProof
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open OriginalRawSyntaxTransportInternalVariableLeafProof OriginalRawSyntaxTransportInternalVariableEraseLeafProof
open OriginalRawSyntaxTransportInternalVariableSpecSyntaxProof OriginalRawSyntaxTransportInternalVariableSpecProof
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open OriginalRawSyntaxTransportInternalFoldLeafProof

theorem variableRanksEqual (erasing : Bool) (raw transformed before after index transformedIndex : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw index)))
    (ht : Nonempty (Derivation body Delta (graph1 variableConstructor transformed transformedIndex)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  have hb := rankVariableForward raw before index hc hb
  have ha := rankVariableForward transformed after transformedIndex ht ha
  simp only [equalEqn] at hb ha
  obtain ⟨hb⟩ := hb
  obtain ⟨ha⟩ := ha
  apply relationOfEqual erasing after before
  simpa only [equalEqn] using
    (Nonempty.intro (InternalTagArithmeticSupportProof.trans ha (InternalTagArithmeticSupportProof.symm hb)))

theorem variableBottomRanks (raw transformed before after index d : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw index)))
    (ht : Nonempty (Derivation body Delta (graph1 bottomConstructor transformed d)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation true after before)) := by
  apply relationTransport true after before z (numeral 1)
    (rankBottomForward transformed after d ht ha) (rankVariableForward raw before index hc hb)
  exact InternalSquareRootArithmeticSupportProof.rightSuccessor z (suc z)
    ⟨InternalQuotientComparisonProof.equalToNext (InternalTagArithmeticSupportProof.refl z)⟩

theorem variableShiftTransport (raw transformed before after d k index : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw index)))
    (ht : Nonempty (Derivation body Delta (graph3 (leaf .shift) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation false after before)) := by
  apply formulaCases (InternalLessThan.strictLess index k)
  · have hl : Nonempty (Derivation body (InternalLessThan.strictLess index k :: Delta)
        (InternalLessThan.strictLess index k)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv := shiftLeafForwardAt raw transformed d k index index (withHyp hc _)
      (shiftChoiceBelow raw d k index (withHyp hc _) hl) (withHyp ht _)
    exact variableRanksEqual false raw transformed before after index index
      (withHyp hc _) hv (withHyp hb _) (withHyp ha _)
  · have hn : Nonempty (Derivation body ((InternalLessThan.strictLess index k).not :: Delta)
        (InternalLessThan.strictLess index k).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv := shiftLeafForwardAt raw transformed d k index (suc index) (withHyp hc _)
      (shiftChoiceNotBelow raw d k index (withHyp hc _) hn) (withHyp ht _)
    exact variableRanksEqual false raw transformed before after index (suc index)
      (withHyp hc _) hv (withHyp hb _) (withHyp ha _)

theorem variableEraseTransport (raw transformed before after d k index : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw index)))
    (ht : Nonempty (Derivation body Delta (graph3 (leaf .erase) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation true after before)) := by
  apply indexCases index k
  · have hl : Nonempty (Derivation body (InternalLessThan.strictLess index k :: Delta)
        (InternalLessThan.strictLess index k)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv := eraseLeafBelowForward raw transformed d k index (withHyp hc _) hl (withHyp ht _)
    exact variableRanksEqual true raw transformed before after index index
      (withHyp hc _) hv (withHyp hb _) (withHyp ha _)
  · have he : Nonempty (Derivation body (equal index k :: Delta) (equal index k)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv := eraseLeafEqualForward raw transformed d k index (withHyp hc _) he (withHyp ht _)
    exact variableBottomRanks raw transformed before after index d
      (withHyp hc _) hv (withHyp hb _) (withHyp ha _)
  · have hg : Nonempty (Derivation body (InternalLessThan.strictLess k index :: Delta)
        (InternalLessThan.strictLess k index)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv := eraseAbovePrevious raw transformed d k index (withHyp hc _) hg (withHyp ht _)
    apply previousCases transformed index _ hv
    intro beta j Theta previous hj _ hprevious
    rw [rankRelationRename]
    have hc' := renameInto (withHyp hc (InternalLessThan.strictLess k index)) j Theta hj
    have hb' := renameInto (withHyp hb (InternalLessThan.strictLess k index)) j Theta hj
    have ha' := renameInto (withHyp ha (InternalLessThan.strictLess k index)) j Theta hj
    rw [graph1Rename] at hc' hb' ha'
    exact variableRanksEqual true (raw.relabel j) (transformed.relabel j) (before.relabel j) (after.relabel j)
      (index.relabel j) previous hc' hprevious hb' ha'

theorem variableTransport (erasing : Bool) (raw transformed before after d k index : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw index)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  have harity := variableArity (.projection 0) raw index (Fin.cons raw Fin.elim0)
    (projectionValue 0 (Fin.cons raw Fin.elim0)) hc
  have hleaf := leafForward (transformMode erasing) d k raw transformed harity ht
  cases erasing with
  | false => exact variableShiftTransport raw transformed before after d k index hc hleaf hb ha
  | true => exact variableEraseTransport raw transformed before after d k index hc hleaf hb ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportVariableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportVariableProof
