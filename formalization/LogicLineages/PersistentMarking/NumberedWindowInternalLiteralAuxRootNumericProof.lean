module
public import LogicLineages.PersistentMarking.NumberedWindowRootDispatchAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootNumericProof
open NumberedWindowRootDispatchAlgorithm (fixed parts)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowFieldAlgorithm (unpackNode packNode pack)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
  (cellAt splitUnpack emptyUnpack)
open NumberedWindowInternalSparseFieldParserRawPairProof (encodedPair)

private theorem unpackPacked (xs : List Nat) : NumberedWindowFieldAlgorithm.unpack (pack xs) = some xs := by
  induction xs with
  | nil => exact emptyUnpack
  | cons x xs ih =>
    change NumberedWindowFieldAlgorithm.unpack (pair x (pack xs) + 1) = _
    rw [splitUnpack (cellAt x (pack xs)),ih]
    rfl

theorem packedReads (tag : Nat) (xs : List Nat) :
    unpackNode (packNode tag xs) = some (tag,xs) := by
  simp [packNode,unpackNode,encodedPair,unpackPacked]

/-- The six genuine non-application root rules reject every raw
auxiliary source, independently of the payload and target. -/
theorem exact_AuxiliaryRejectsOtherRootParts (entries : Entries) (heads : List Nat)
    (q r dom cod fn arg tag : Nat) (fields : List Nat)
    (h : unpackNode q = some (6,[dom,cod,fn,arg])) (low : tag < 6) :
    parts (fixed entries heads) q r tag fields = false := by
  unfold parts
  split
  · simp [fixed,NumberedWindowMarkRootAlgorithm.mark,NumberedWindowMarkRootAlgorithm.markBody,
      NumberedWindowMarkRootAlgorithm.guarded,h]
  · simp [fixed,NumberedWindowMarkRootAlgorithm.lower,NumberedWindowMarkRootAlgorithm.lowerBody,
      NumberedWindowMarkRootAlgorithm.guarded,h]
  · simp only [fixed,NumberedWindowSelectAlgorithm.select,
      NumberedWindowMarkRootAlgorithm.guarded,h]
    cases NumberedWindowRootDispatchAlgorithm.flagView _ <;>
      cases NumberedWindowAddressAlgorithm.contextView _ <;> simp [NumberedWindowSelectAlgorithm.body]
  · simp only [fixed,NumberedWindowCopyAlgorithm.copy,
      NumberedWindowMarkRootAlgorithm.guarded,h]
    cases unpackNode r <;> simp [NumberedWindowCopyAlgorithm.copyRows]
  · simp only [fixed,NumberedWindowStatRootAlgorithm.stat,
      NumberedWindowMarkRootAlgorithm.guarded,h]
    cases unpackNode r <;> simp [NumberedWindowStatRootAlgorithm.rows]
  · simp [fixed,NumberedWindowBinderRootAlgorithm.fabs,NumberedWindowBinderRootAlgorithm.fabsRow,
      NumberedWindowMarkRootAlgorithm.guarded,h]
  · omega
  · omega
  · rfl

/-- A direct beta step at a raw auxiliary source requires that the
actual function field parses with the literal lambda tag. Malformed
function values are included in the exclusion. -/
theorem exact_AuxiliaryBetaRequiresLambda (q r dom cod fn arg : Nat)
    (h : unpackNode q = some (6,[dom,cod,fn,arg]))
    (nonLam : ¬ ∃ fs, unpackNode fn = some (2,fs)) :
    NumberedWindowBinderRootAlgorithm.beta q r = false := by
  simp only [NumberedWindowBinderRootAlgorithm.beta,NumberedWindowMarkRootAlgorithm.guarded,h]
  change ((_ && _) && (unpackNode fn).any (NumberedWindowBinderRootAlgorithm.betaRows r (6,[dom,cod,fn,arg]))) = _
  cases hf : unpackNode fn with
  | none => simp
  | some x =>
    obtain ⟨tag,fields⟩ := x
    have neq : tag ≠ 2 := fun ht => nonLam ⟨fields,by simpa only [ht] using hf⟩
    simp [NumberedWindowBinderRootAlgorithm.betaRows,neq]

/-- The original bottom rule writes the literal bottom at the same
auxiliary result field; this is not an equality of quotient addresses. -/
theorem exact_AuxiliaryBottomPart (q r dom cod fn arg : Nat)
    (h : unpackNode q = some (6,[dom,cod,fn,arg])) :
    NumberedWindowMarkRootAlgorithm.bottom q r =
      NumberedWindowMarkRootAlgorithm.guarded q r (q != packNode 3 [cod] && packNode 3 [cod] == r) := by
  simp [NumberedWindowMarkRootAlgorithm.bottom,NumberedWindowAnnotationAlgorithm.annotations,
    NumberedWindowAnnotationAlgorithm.termNext,NumberedWindowAnnotationAlgorithm.termParts,h]

#print axioms exact_AuxiliaryRejectsOtherRootParts
#print axioms exact_AuxiliaryBetaRequiresLambda
#print axioms exact_AuxiliaryBottomPart
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootNumericProof
