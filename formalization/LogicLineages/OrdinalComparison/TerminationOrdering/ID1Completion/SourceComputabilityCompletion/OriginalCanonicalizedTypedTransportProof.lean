module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportPackedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (selectedTyped)
open InternalParameterizedCanonicalResultFold (foldGraph)
open OriginalLambdaConstructorGraphSyntaxProof (andLeft andRight)
open OriginalCanonicalizedTypedTransportPackedProof
open OriginalCanonicalizedTypedTransportTargets
open OriginalTransparentDecoderValidatorCollapse
open OriginalContextInsertion OriginalRawSyntaxTransport
open SourceComputabilityFormulaSupportProof (numeral)

theorem actualOriginalCanonicalizedTypedPackedWeakening :
    ActualOriginalCanonicalizedTypedPackedWeakening := by
  intro p H G W body alpha Delta d cutoff gamma extended c parameter extendedParameter input shifted out typ
  let data := selected p H G W
  let A := Insert d cutoff gamma extended ⊓
    (graph2 InternalPairing.pairing parameter c gamma ⊓
      (graph2 InternalPairing.pairing extendedParameter c extended ⊓
        (graph2 shiftPackedRaw shifted cutoff input ⊓
          (graph3 (selectedTyped data) (numeral 1) input typ parameter ⊓
            foldGraph data out shifted extendedParameter))))
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨ho⟩ := weakeningAt p H G W
    d cutoff gamma extended c parameter extendedParameter input shifted out typ
    (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h)))
    (andLeft (andRight (andRight (andRight h))))
    (andLeft (andRight (andRight (andRight (andRight h)))))
    (andRight (andRight (andRight (andRight (andRight h)))))
  exact ⟨Derivation.implicationIntroduction ho⟩

theorem actualOriginalCanonicalizedTypedPackedErasure :
    ActualOriginalCanonicalizedTypedPackedErasure := by
  intro p H G W body alpha Delta d cutoff gamma extended c parameter extendedParameter input erased out typ
  let data := selected p H G W
  let A := Insert d cutoff gamma extended ⊓
    (graph2 InternalPairing.pairing parameter c gamma ⊓
      (graph2 InternalPairing.pairing extendedParameter c extended ⊓
        (graph3 erasePackedRaw erased d cutoff input ⊓
          (graph3 (selectedTyped data) (numeral 1) input typ extendedParameter ⊓
            foldGraph data out erased parameter))))
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨ho⟩ := erasureAt p H G W
    d cutoff gamma extended c parameter extendedParameter input erased out typ
    (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h)))
    (andLeft (andRight (andRight (andRight h))))
    (andLeft (andRight (andRight (andRight (andRight h)))))
    (andRight (andRight (andRight (andRight (andRight h)))))
  exact ⟨Derivation.implicationIntroduction ho⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportProof
