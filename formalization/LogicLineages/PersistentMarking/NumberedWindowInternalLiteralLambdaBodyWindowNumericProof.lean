module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalSourceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalSourceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowMemoChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaBodyWindowNumericProof
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowInternalSparseTypedRawTargets (packedWindow)
open NumberedWindowInternalAuxWindowMemoTargets (intrinsicWindow intrinsicType)
open NumberedWindowInternalCoverLambdaLexicalSourceProof (exact_CoverLambdaPackedLexicalProvenance)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt)
open NumberedWindowInternalAuxWindowMemoChecks (exact_PackedIntrinsicProjection)
open NumberedWindowInternalSparseFieldParserRawPairProof (encodedPair)

private theorem arrowInjectivity {d a b : Nat} (eq : arrow d a = arrow d b) : a = b := by
  change pair d a + 1 = pair d b + 1 at eq
  have z : pair d a = pair d b := Nat.add_right_cancel eq
  have h := encodedPair d a
  rw [z,encodedPair d b] at h
  exact (congrArg Prod.snd (Option.some.inj h)).symm

/-- The numeric original type in an actual lambda window is the
stored binder and the exact body result, after extending the same
lexical context. This is before any claim about open typing reports. -/
theorem exact_LiteralOriginalLambdaBodyWindow (s : Settings) (ctx ty raw d a : Nat)
    (view : unpackNode raw = some (2,[d,a]))
    (typed : packedWindow s ctx ty raw = true) :
    ty = arrow d (intrinsicType a) ∧
    packedWindow s (pair d ctx + 1) (intrinsicType a) a = true := by
  have selected : intrinsicWindow s ctx raw = ty + 1 := by
    rw [exact_PackedIntrinsicProjection] at typed
    exact beq_iff_eq.mp typed
  have live : intrinsicWindow s ctx raw ≠ 0 := by rw [selected]; omega
  obtain ⟨g,decoded,_,inner,outer⟩ := exact_CoverLambdaPackedLexicalProvenance s ctx raw d a view live
  have ctxEq : NumberedWindowFieldAlgorithm.pack g = ctx :=
    (NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof.packOfUnpack ctx decoded).symm
  have push : NumberedWindowFieldAlgorithm.pack (d :: g) = pair d ctx + 1 := by
    change pair d (NumberedWindowFieldAlgorithm.pack g) + 1 = _
    rw [ctxEq]
  refine ⟨Nat.add_right_cancel (selected.symm.trans outer),?_⟩
  rw [exact_PackedIntrinsicProjection,← push,inner]
  simp

theorem exact_LiteralOriginalLambdaBothBodyWindows (s : Settings) (ctx ty q r d a b : Nat)
    (left : unpackNode q = some (2,[d,a])) (right : unpackNode r = some (2,[d,b]))
    (source : packedWindow s ctx ty q = true) (dest : packedWindow s ctx ty r = true) :
    ∃ cod, ty = arrow d cod ∧ packedWindow s (pair d ctx + 1) cod a = true ∧
      packedWindow s (pair d ctx + 1) cod b = true := by
  obtain ⟨p,wa⟩ := exact_LiteralOriginalLambdaBodyWindow s ctx ty q d a left source
  obtain ⟨q',wb⟩ := exact_LiteralOriginalLambdaBodyWindow s ctx ty r d b right dest
  have same := arrowInjectivity (p.symm.trans q')
  exact ⟨intrinsicType a,p,wa,same.symm ▸ wb⟩

#print axioms exact_LiteralOriginalLambdaBodyWindow
#print axioms exact_LiteralOriginalLambdaBothBodyWindows
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaBodyWindowNumericProof
