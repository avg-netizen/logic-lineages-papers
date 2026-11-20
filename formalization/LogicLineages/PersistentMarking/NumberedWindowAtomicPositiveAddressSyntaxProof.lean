module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveAddressSyntaxProof
open NumberedWindowAtomicPositiveTargets
open NumberedWindowAddressAlgorithm (addressView contextView typeBit)
open NumberedWindowFieldAlgorithm (pack unpack)
open NumberedWindowAtomicRawStepFieldProof (nodePacked)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (packOfUnpack)

theorem literalView : ExactLiteralAtomicAddressView := by
  intro context result payload
  rw [packedAddress,addressView,nodePacked] <;> rfl

private theorem contextUnpack {raw : Nat} {ctx : List Nat}
    (h : contextView raw = some ctx) : unpack raw = some ctx := by
  unfold contextView at h
  cases hu : unpack raw with
  | none => simp [hu] at h
  | some xs =>
    have parsed : (∀ x ∈ xs, typeBit x = true) ∧ xs = ctx := by
      simpa [hu] using h
    exact congrArg some parsed.2

theorem contextCode {raw : Nat} {ctx : List Nat} (h : contextView raw = some ctx) :
    raw = pack ctx := packOfUnpack raw (contextUnpack h)

end LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveAddressSyntaxProof
