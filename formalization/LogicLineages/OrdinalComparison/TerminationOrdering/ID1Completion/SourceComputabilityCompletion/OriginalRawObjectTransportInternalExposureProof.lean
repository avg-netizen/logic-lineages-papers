module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionTotalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalExposureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalGraphCompositionTotalityProof InternalRecursionClosureProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof OriginalRawObjectTransport
open OriginalRawObjectTransportInternalSupportProof OriginalRawObjectTransportInternalSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof

/-- Totality constructs the coordinates inside the original arithmetic
calculus. No native context or native evaluation is an internal premise. -/
theorem actualRawObjectInternalShiftExposure :
    OriginalRawObjectTransportTargets.ActualRawObjectInternalShiftExposure := by
  intro body alpha Delta d input shifted psi ho k
  let xs : Fin 2 → OTerm alpha := Fin.cons d (Fin.cons input Fin.elim0)
  apply supplyOutputs body 2 4 (fun i => OrdinaryArithmetic.graphFormula (shiftQueries i))
    (fun i => (actualOriginalPrograms body 2 (shiftQueries i)).1) alpha Delta xs psi
  intro beta j Theta ys hj hs
  apply k beta j Theta hj (ys 0) (ys 1) (ys 2) (ys 3)
  have ho' := binaryRename shiftObjectRaw shifted d input ho j Theta hj
  have hs' : ∀ i, Nonempty (Derivation body Theta
      (programGraph (shiftQueries i) (ys i)
        (Fin.cons (d.relabel j) (Fin.cons (input.relabel j) Fin.elim0)))) :=
    fun i => queryTwoRename (shiftQueries i) d input j Theta (ys i) (hs i)
  exact shiftRecoveredAt (d.relabel j) (input.relabel j) (shifted.relabel j) ys hs' ho' 

theorem actualRawObjectInternalEraseExposure :
    OriginalRawObjectTransportTargets.ActualRawObjectInternalEraseExposure := by
  intro body alpha Delta d input erased gamma packed extendedGamma psi hp hc he k
  let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
  apply supplyOutputs body 1 1 (fun _ => OrdinaryArithmetic.graphFormula erasedPayload)
    (fun _ => (actualOriginalPrograms body 1 erasedPayload).1) alpha Delta xs psi
  intro beta j Theta ys hj hs
  apply k beta j Theta hj (ys 0)
  have hp' := binaryRename InternalPairing.pairing input extendedGamma packed hp j Theta hj
  have hc' := binaryRename InternalListCodec.consCode extendedGamma d gamma hc j Theta hj
  have he' := unaryRename eraseObjectRaw erased input he j Theta hj
  have hq := queryOneRename erasedPayload input j Theta (ys 0) (hs 0)
  exact eraseRecoveredAt (d.relabel j) (input.relabel j) (erased.relabel j)
    (gamma.relabel j) (packed.relabel j) (extendedGamma.relabel j) (ys 0) hp' hc' he' hq

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalExposureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalExposureProof
