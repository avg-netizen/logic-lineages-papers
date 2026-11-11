module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportInterfaceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open OriginalContextInsertion OriginalRawSyntaxTransport
open OriginalLambdaConstructorGraphSyntaxProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalUniverseDecoderTransportTargets OriginalUniverseDecoderTransport
open OriginalUniverseDecoderTransportInductionProof OriginalUniverseDecoderTransportInterfaceProof

theorem actualOriginalUniverseInternalTermWeakening : ActualOriginalUniverseInternalTermWeakening := by
  intro body H M W alpha d cutoff gamma extended typ raw shifted c
  let A := Insert d cutoff gamma extended ⊓
    (graph2 shiftRaw shifted cutoff raw ⊓ Accepted H M W false typ raw gamma c)
  have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨out⟩ := weakeningAt H M W false d cutoff gamma extended typ raw shifted c
    (allRawTransport H M W false raw) (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction out⟩

theorem actualOriginalUniverseInternalArgumentsWeakening : ActualOriginalUniverseInternalArgumentsWeakening := by
  intro body H M W alpha d cutoff gamma extended types raw shifted c
  let A := Insert d cutoff gamma extended ⊓
    (graph2 shiftRaw shifted cutoff raw ⊓ Accepted H M W true types raw gamma c)
  have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨out⟩ := weakeningAt H M W true d cutoff gamma extended types raw shifted c
    (allRawTransport H M W false raw) (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction out⟩

theorem actualOriginalUniverseInternalTermErasure : ActualOriginalUniverseInternalTermErasure := by
  intro body H M W alpha d cutoff gamma extended typ raw erased c
  let A := Insert d cutoff gamma extended ⊓
    (graph3 eraseRaw erased d cutoff raw ⊓ Accepted H M W false typ raw extended c)
  have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨out⟩ := erasureAt H M W false d cutoff gamma extended typ raw erased c
    (allRawTransport H M W true raw) (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction out⟩

theorem actualOriginalUniverseInternalArgumentsErasure : ActualOriginalUniverseInternalArgumentsErasure := by
  intro body H M W alpha d cutoff gamma extended types raw erased c
  let A := Insert d cutoff gamma extended ⊓
    (graph3 eraseRaw erased d cutoff raw ⊓ Accepted H M W true types raw extended c)
  have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨out⟩ := erasureAt H M W true d cutoff gamma extended types raw erased c
    (allRawTransport H M W true raw) (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction out⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportProof
