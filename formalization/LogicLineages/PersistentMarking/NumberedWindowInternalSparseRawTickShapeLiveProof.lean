module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeLiveProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseRawFunctionFrame (chosenFrame)
open NumberedWindowInternalSparseRawTick
open NumberedWindowInternalSparseRawTickShapeTargets
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (goodRename)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (zeroFlagShape zeroFrameShape)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The actual live dispatcher on an arbitrary ternary tape. The two
nested controls are split by original totality plus the arithmetic
zero/successor rule; each selected leaf is one of the three literal
emitters. No control or callback value is interpreted. -/
theorem liveShape (p other : Program 3) (out : OTerm α) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph (liveTick p other) out xs))) :
    Nonempty (Derivation body Γ (goodState out)) := by
  let fallback : Program 3 := emitState (constantZero 3) other
  let rooted : Program 3 := emitState (rootCall p) (constantZero 3)
  let inner : Program 3 := branch rootTest fallback rooted
  let chosen : Program 3 := emitState (constantZero 3) chosenFrame
  apply optionGraphCases tagFiveTest xs (goodState out)
  · intro β j Δ hj hz
    rw [goodRename]
    have h' := renameInto h j Δ hj
    rw [programRename] at h'
    have hin := zeroBranchElim tagFiveTest inner chosen (out.relabel j)
      (fun i => (xs i).relabel j) hz h'
    apply optionGraphCases rootTest (fun i => (xs i).relabel j) (goodState (out.relabel j))
    · intro γ k Θ hk hz2
      rw [goodRename]
      have hin' := renameInto hin k Θ hk
      rw [programRename] at hin'
      exact zeroFlagShape other _ _
        (zeroBranchElim rootTest fallback rooted ((out.relabel j).relabel k) _ hz2 hin')
    · intro γ k Θ u hk hs2
      rw [goodRename]
      have hin' := renameInto hin k Θ hk
      rw [programRename] at hin'
      exact zeroFrameShape (rootCall p) _ _
        (successorBranchElim rootTest fallback rooted ((out.relabel j).relabel k) u _ hs2 hin')
  · intro β j Δ u hj hs
    rw [goodRename]
    have h' := renameInto h j Δ hj
    rw [programRename] at h'
    exact zeroFlagShape chosenFrame _ _
      (successorBranchElim tagFiveTest inner chosen (out.relabel j) u
        (fun i => (xs i).relabel j) hs h')

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeLiveProof
