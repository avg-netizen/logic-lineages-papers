module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalExposureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalPackedCancellationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalCancellationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof OriginalLambdaConstructorGraphSyntaxProof
open InternalTagArithmeticSyntaxProof (eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawObjectTransport OriginalRawObjectTransportInternalSupportProof
open OriginalRawObjectTransportInternalExposureProof OriginalRawObjectTransportInternalPackedCancellationProof

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The context inverse is paid by the actual cons destructors, while packed
cancellation uses the independently accepted all-raw internal syntax theorem. -/
theorem objectRightInverse (d input shifted : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 shiftObjectRaw shifted d input))) :
    Nonempty (Derivation body Delta (graph1 eraseObjectRaw input shifted)) := by
  apply actualRawObjectInternalShiftExposure body alpha Delta d input shifted _ hs
  intro beta j Theta hj gamma packed extendedGamma shiftedPacked hf
  rw [graph1Rename]
  have hp := andLeft hf
  have hc := andLeft (andRight hf)
  have ht := andLeft (andRight (andRight hf))
  have ho := andRight (andRight (andRight hf))
  exact eraseObjectBackward (d.relabel j) (shifted.relabel j) (input.relabel j)
    gamma shiftedPacked extendedGamma packed ho hc
    (packedRightInverse packed shiftedPacked (d.relabel j) (numeral 0) ht) hp

theorem internalCancellation (positive : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (d input shifted erased : OTerm alpha) :
    Nonempty (Derivation positive Delta
      ((graph2 shiftObjectRaw shifted d input ⊓ graph1 eraseObjectRaw erased shifted).imp
        (equal erased input))) := by
  let A := graph2 shiftObjectRaw shifted d input ⊓ graph1 eraseObjectRaw erased shifted
  have h : Derivation positive (A :: Delta) A := Derivation.hypothesis List.mem_cons_self
  have hi := objectRightInverse d input shifted ⟨Derivation.conjunctionLeft h⟩
  obtain ⟨he⟩ := valueUnique eraseObjectRaw erased input (Fin.cons shifted Fin.elim0)
    ⟨Derivation.conjunctionRight h⟩ hi
  exact ⟨Derivation.implicationIntroduction (by simpa only [equalEqn] using he)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalCancellationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalCancellationProof
