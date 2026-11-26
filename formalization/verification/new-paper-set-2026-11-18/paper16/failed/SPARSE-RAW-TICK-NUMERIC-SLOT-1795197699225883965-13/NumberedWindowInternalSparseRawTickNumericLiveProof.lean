module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickNumericASTProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericThinChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickNumericLiveProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowRawContextAlgorithm (tick RawRoot)
open NumberedWindowInternalSparseRawTick
open NumberedWindowInternalSparseRawTickTargets
open NumberedWindowInternalSparseRawFunctionFrame (tagFiveNext encodeFrame)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape)
open NumberedWindowInternalSparseRawFunctionFrameNumericThinChecks (exact_AllRawFunctionFrame)
open NumberedWindowInternalSparseRawTickNumericASTProof
  (rootOne rootZero tagFiveOne tagFiveZero liveValue actualRootValue)

private theorem originalFallback (root : RawRoot) (flag : Bool) (q w r : Nat)
    (noRoot : ¬ ∃ a, unpackNode w = some (0,[a])) :
    tick root (flag,some (q,w,r)) = (false,fallbackValue q w r) := by
  cases seen : unpackNode w with
  | none => simp [tick,fallbackValue,seen]
  | some data =>
    rcases data with ⟨_ | tag,fs⟩
    · rcases fs with _ | ⟨p,_ | ⟨x,xs⟩⟩
      · simp [tick,fallbackValue,seen]
      · exact False.elim (noRoot ⟨p,seen⟩)
      · simp [tick,fallbackValue,seen]
    · simp [tick,fallbackValue,seen]

theorem live : ExactOriginalLiveTick := by
  intro root p other hp ho flag q w r
  rw [liveValue]
  by_cases five : ∃ child, unpackNode w = some (5,[child])
  · obtain ⟨child,seen⟩ := five
    have yes := (tagFiveOne q w r).mpr ⟨child,seen⟩
    rw [yes,if_neg (by decide : (1 : Nat) ≠ 0),exact_AllRawFunctionFrame]
    simp [tick,tagFiveNext,encodeState,seen]
  · rw [tagFiveZero q w r five,if_pos rfl]
    by_cases base : ∃ a, unpackNode w = some (0,[a])
    · obtain ⟨payload,seen⟩ := base
      have yes := (rootOne q w r).mpr ⟨payload,seen⟩
      rw [yes,if_neg (by decide : (1 : Nat) ≠ 0),actualRootValue root p hp q w r payload seen]
      simp [tick,encodeState,encodeFrame,seen]
    · rw [rootZero q w r base,if_pos rfl,ho,originalFallback root flag q w r base] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickNumericLiveProof
