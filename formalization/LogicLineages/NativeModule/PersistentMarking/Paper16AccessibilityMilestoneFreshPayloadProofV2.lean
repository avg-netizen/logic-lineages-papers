module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshPayloadTargetsV2
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastShapeProof

/-! Proofs of the frozen `FreshPayloadIsNamedLeaf` and `FreeSeedSelfLeast`
(`Paper16AccessibilityMilestoneFreshPayloadTargetsV2`; Fable B2, 27 November 2026). The first is
definitional. The second composes the accepted `freeAtom`, `queryAtInput` and
`exact_OpenLiteralAtomicGuardedLeastSingleton`. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshPayloadProofV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalLiteralAtomicRawShapeProof (freeTerm)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralAtomicLeastShapeProof
  (freeAtom queryAtInput exact_OpenLiteralAtomicGuardedLeastSingleton)
open Paper16AccessibilityMilestoneFreshPayloadTargetsV2

theorem exact_FreshPayloadIsNamedLeaf : FreshPayloadIsNamedLeaf := by
  intro α ctx dom name
  rfl

/-- The named leaf with tag zero is the free term of the atomic line. -/
private theorem namedIsFree {α : Type} (a n : OTerm α) : namedTerm 0 a n = freeTerm a n := rfl

theorem exact_FreeSeedSelfLeast : FreeSeedSelfLeast := by
  intro L body α Γ ctx ty a n t held
  rw [namedIsFree] at held ⊢
  exact exact_OpenLiteralAtomicGuardedLeastSingleton L ctx ty (freeTerm a n) t held
    (queryAtInput (freeTerm a n) t (freeAtom a n))

#print axioms exact_FreshPayloadIsNamedLeaf
#print axioms exact_FreeSeedSelfLeast

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFreshPayloadProofV2
