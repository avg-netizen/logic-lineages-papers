module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankPackedQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankPackedTransportProof
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
open OriginalRawVariableRankPackedQueryProof OriginalRawVariableRankTransportProof
open OriginalRawVariableRankSupportProof
open OriginalRawSyntaxTransportInternalPackedProof OriginalRawSyntaxTransportInternalInterfaceSupportProof

theorem rankShiftPackedForwardAt (packed shifted tau raw shiftedRaw rank k : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed tau raw)))
    (ht : Nonempty (Derivation body Delta (graph2 shiftRaw shiftedRaw k raw)))
    (hs : Nonempty (Derivation body Delta (graph2 shiftPackedRaw shifted k packed)))
    (hr : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank shifted))) :
    Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank packed)) := by
  have hp' := shiftPackedForward packed shifted tau raw shiftedRaw k hp ht hs
  exact rankPackedBackward packed rank tau raw hp
    (rankShiftForward raw shiftedRaw rank k ht (rankPackedForward shifted rank tau shiftedRaw hp' hr))

theorem rankShiftPackedBackwardAt (packed shifted tau raw shiftedRaw rank k : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed tau raw)))
    (ht : Nonempty (Derivation body Delta (graph2 shiftRaw shiftedRaw k raw)))
    (hs : Nonempty (Derivation body Delta (graph2 shiftPackedRaw shifted k packed)))
    (hr : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank packed))) :
    Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank shifted)) := by
  have hp' := shiftPackedForward packed shifted tau raw shiftedRaw k hp ht hs
  exact rankPackedBackward shifted rank tau shiftedRaw hp'
    (rankShiftBackward raw shiftedRaw rank k ht (rankPackedForward packed rank tau raw hp hr))

theorem rankShiftPackedForward (packed shifted rank k : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 shiftPackedRaw shifted k packed)))
    (hr : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank shifted))) :
    Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank packed)) := by
  apply packedTransformCases (fold .shift) z k packed _
  intro beta j Theta tau raw shiftedRaw hj hp ht
  rw [graph1Rename]
  have hs' := renameInto hs j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph2Rename] at hs'
  rw [graph1Rename] at hr'
  simp only [zRelabel] at ht
  exact rankShiftPackedForwardAt (packed.relabel j) (shifted.relabel j) tau raw shiftedRaw (rank.relabel j) (k.relabel j)
    hp (zeroFirstBackward (fold .shift) shiftedRaw (k.relabel j) raw ht) hs' hr'

theorem rankShiftPackedBackward (packed shifted rank k : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 shiftPackedRaw shifted k packed)))
    (hr : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank packed))) :
    Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank shifted)) := by
  apply packedTransformCases (fold .shift) z k packed _
  intro beta j Theta tau raw shiftedRaw hj hp ht
  rw [graph1Rename]
  have hs' := renameInto hs j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph2Rename] at hs'
  rw [graph1Rename] at hr'
  simp only [zRelabel] at ht
  exact rankShiftPackedBackwardAt (packed.relabel j) (shifted.relabel j) tau raw shiftedRaw (rank.relabel j) (k.relabel j)
    hp (zeroFirstBackward (fold .shift) shiftedRaw (k.relabel j) raw ht) hs' hr'

theorem rankErasePackedNonincreaseAt (packed erased tau raw erasedRaw before after d k : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed tau raw)))
    (ht : Nonempty (Derivation body Delta (graph3 eraseRaw erasedRaw d k raw)))
    (he : Nonempty (Derivation body Delta (graph3 erasePackedRaw erased d k packed)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw before packed)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw after erased))) :
    Nonempty (Derivation body Delta (RankNonincrease after before)) := by
  have hp' := erasePackedForward packed erased tau raw erasedRaw d k hp ht he
  exact rankEraseNonincrease raw erasedRaw before after d k ht
    (rankPackedForward packed before tau raw hp hb)
    (rankPackedForward erased after tau erasedRaw hp' ha)

theorem rankErasePackedNonincrease (packed erased before after d k : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph3 erasePackedRaw erased d k packed)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw before packed)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw after erased))) :
    Nonempty (Derivation body Delta (RankNonincrease after before)) := by
  apply packedTransformCases (fold .erase) d k packed _
  intro beta j Theta tau raw erasedRaw hj hp ht
  rw [rankNonincreaseRename]
  have he' := renameInto he j Theta hj
  have hb' := renameInto hb j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [graph3Rename] at he'
  rw [graph1Rename] at hb' ha'
  exact rankErasePackedNonincreaseAt (packed.relabel j) (erased.relabel j) tau raw erasedRaw
    (before.relabel j) (after.relabel j) (d.relabel j) (k.relabel j) hp ht he' hb' ha'

theorem actualRawVariableRankShiftPacked : OriginalRawVariableRankTargets.ActualRawVariableRankShiftPacked := by
  intro positive alpha Delta raw shifted rank k
  let C := graph2 shiftPackedRaw shifted k raw
  let G := graph1 variableRankPackedRaw rank shifted
  let R := graph1 variableRankPackedRaw rank raw
  have hcG : Nonempty (Derivation positive (G :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive (R :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := rankShiftPackedForward raw shifted rank k hcG ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := rankShiftPackedBackward raw shifted rank k hcR ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

theorem actualRawVariableRankErasePacked : OriginalRawVariableRankTargets.ActualRawVariableRankErasePacked := by
  intro positive alpha Delta raw erased before after d k
  let A := graph3 erasePackedRaw erased d k raw ⊓
    (graph1 variableRankPackedRaw before raw ⊓ graph1 variableRankPackedRaw after erased)
  have h : Nonempty (Derivation positive (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := rankErasePackedNonincrease raw erased before after d k (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankPackedTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankPackedTransportProof
