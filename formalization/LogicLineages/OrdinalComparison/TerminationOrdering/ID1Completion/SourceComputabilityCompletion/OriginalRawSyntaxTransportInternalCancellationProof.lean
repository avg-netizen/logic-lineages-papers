module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationIntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationAtProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (zRelabel)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalTargets OriginalRawSyntaxTransportInternalCancellation
open OriginalRawSyntaxTransportInternalCancellationSyntaxProof OriginalRawSyntaxTransportInternalCancellationBindingProof
open OriginalRawSyntaxTransportInternalCancellationIntroductionProof OriginalRawSyntaxTransportInternalCancellationAtProof
open OriginalRawSyntaxTransportInternalCancellationLeafProof OriginalRawSyntaxTransportInternalCancellationTagsProof
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem unaryRightInverse (raw shifted d k : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) raw)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  apply orCases (arityOneTags raw ha)
  · intro Theta inc ht
    exact lambdaTagRightInverse raw shifted d k (weakenProof hi inc) ht (weakenProof hs inc)
  · intro Theta inc ht
    exact ordinaryTagRightInverse raw shifted d k (weakenProof hi inc) ht (weakenProof hs inc)

theorem binaryRightInverse (raw shifted d k : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) raw)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  apply orCases (arityTwoTags raw ha)
  · intro Theta inc ht
    exact applicationTagRightInverse raw shifted d k (weakenProof hi inc) ht (weakenProof hs inc)
  · intro Theta inc ht
    apply orCases ht
    · intro Xi inc' hn
      exact numberedTagRightInverse raw shifted d k (weakenProof (weakenProof hi inc) inc') hn
        (weakenProof (weakenProof hs inc) inc')
    · intro Xi inc' hn
      exact consTagRightInverse raw shifted d k (weakenProof (weakenProof hi inc) inc') hn
        (weakenProof (weakenProof hs inc) inc')

theorem cancellationStep (raw shifted d k : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  apply arityCases raw
  · intro beta j Theta hj ha
    rw [graph3Rename]
    have hs' := renameInto hs j Theta hj
    simp only [graph3Rename,numeral,zRelabel] at hs'
    exact leafFoldRightInverse (raw.relabel j) (shifted.relabel j) (d.relabel j) (k.relabel j) ha hs'
  · intro beta j Theta hj ha
    rw [graph3Rename]
    have hi' := renameInto hi j Theta hj
    have hs' := renameInto hs j Theta hj
    rw [belowRawRename] at hi'
    simp only [graph3Rename,numeral,zRelabel] at hs'
    exact unaryRightInverse (raw.relabel j) (shifted.relabel j) (d.relabel j) (k.relabel j) hi' ha hs'
  · intro beta j Theta hj ha
    rw [graph3Rename]
    have hi' := renameInto hi j Theta hj
    have hs' := renameInto hs j Theta hj
    rw [belowRawRename] at hi'
    simp only [graph3Rename,numeral,zRelabel] at hs'
    exact binaryRightInverse (raw.relabel j) (shifted.relabel j) (d.relabel j) (k.relabel j) hi' ha hs'

/-- Internal strong induction covers every arithmetic raw natural, including
the frozen malformed and unknown-tag domain. All binder parameters stay bound. -/
theorem allRawCancellation (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw (fold .shift) (fold .erase) raw)) := by
  apply rawInduction (fold .shift) (fold .erase) raw
  intro beta Theta r hi
  apply atRawIntroFrom (fold .shift) (fold .erase) r
  intro gamma j Xi d k shifted hj hs
  have hi' := renameInto hi j Xi hj
  rw [belowRawRename] at hi'
  exact cancellationStep (r.relabel j) shifted d k hi' hs

theorem actualRawSyntaxInternalCancellation : ActualRawSyntaxInternalCancellation := by
  intro positive alpha Delta raw shifted erased d k
  let A := graph2 shiftRaw shifted k raw ⊓ graph3 eraseRaw erased d k shifted
  have h : Derivation positive (A :: Delta) A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨he⟩ := cancellationAt raw shifted erased d k (allRawCancellation raw)
    ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.implicationIntroduction he⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationProof
