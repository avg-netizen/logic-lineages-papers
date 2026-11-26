module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaProvenanceTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowAddressAlgorithm (typeBit)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowCoverBoundsAlgorithm (bounds)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)

/-- Same actually parsed lambda's body slot, earlier syntax row and
unshifted depth/numeral source coordinates. These are numerical facts. -/
def ExactCoverLambdaSourceProvenance : Prop :=
  ∀ (raw ty q : Nat), unpackNode raw = some (2,[ty,q]) →
    q < raw ∧
    (((syntaxBits raw).1 = true ↔ typeBit ty = true ∧ (syntaxBits q).1 = true) ∧
      (bounds raw).1 = ((bounds q).1.1 + 1,(bounds q).1.2))

/-- One calibrated original syntax V and one calibrated measure M on
the actual raw parent and body, without any native-to-object reflection. -/
def ExactCoverLambdaSelectedProvenance : Prop :=
  ∀ (V M : Program 1), TermSyntaxCalibrated V → TermMeasureCalibrated M →
  ∀ (raw ty q : Nat), unpackNode raw = some (2,[ty,q]) → run V raw = 1 →
    q < raw ∧ typeBit ty = true ∧ run V q = 1 ∧
    run M q = Encodable.encode (bounds q).1 ∧
    run M raw = Encodable.encode ((bounds q).1.1+1,(bounds q).1.2)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaProvenanceTargets
