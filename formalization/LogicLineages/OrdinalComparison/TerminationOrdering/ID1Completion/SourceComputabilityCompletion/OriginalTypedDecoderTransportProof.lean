module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportInterfaceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open OriginalContextInsertion OriginalRawSyntaxTransport
open OriginalLambdaConstructorGraphSyntaxProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderTransportTargets OriginalTypedDecoderTransport
open OriginalTypedDecoderTransportInductionProof OriginalTypedDecoderTransportInterfaceProof

theorem actualOriginalTypedInternalTermWeakening : ActualOriginalTypedInternalTermWeakening := by
  intro body H alpha d cutoff gamma extended typ raw shifted
  let A := Insert d cutoff gamma extended ⊓
    (graph2 shiftRaw shifted cutoff raw ⊓ Accepted H false typ raw gamma)
  have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨out⟩ := weakeningAt H false d cutoff gamma extended typ raw shifted
    (allRawTransport H false raw) (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction out⟩

theorem actualOriginalTypedInternalArgumentsWeakening : ActualOriginalTypedInternalArgumentsWeakening := by
  intro body H alpha d cutoff gamma extended types raw shifted
  let A := Insert d cutoff gamma extended ⊓
    (graph2 shiftRaw shifted cutoff raw ⊓ Accepted H true types raw gamma)
  have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨out⟩ := weakeningAt H true d cutoff gamma extended types raw shifted
    (allRawTransport H false raw) (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction out⟩

theorem actualOriginalTypedInternalTermErasure : ActualOriginalTypedInternalTermErasure := by
  intro body H alpha d cutoff gamma extended typ raw erased
  let A := Insert d cutoff gamma extended ⊓
    (graph3 eraseRaw erased d cutoff raw ⊓ Accepted H false typ raw extended)
  have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨out⟩ := erasureAt H false d cutoff gamma extended typ raw erased
    (allRawTransport H true raw) (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction out⟩

theorem actualOriginalTypedInternalArgumentsErasure : ActualOriginalTypedInternalArgumentsErasure := by
  intro body H alpha d cutoff gamma extended types raw erased
  let A := Insert d cutoff gamma extended ⊓
    (graph3 eraseRaw erased d cutoff raw ⊓ Accepted H true types raw extended)
  have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨out⟩ := erasureAt H true d cutoff gamma extended types raw erased
    (allRawTransport H true raw) (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction out⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportProof
