module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericASTProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTickNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch conjunction constantZero)
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowConcreteCheckers (root)
open NumberedWindowFieldAlgorithm (unpackNode packNode)
open NumberedWindowAtomicRawStep (freeRaw bottomRaw)
open NumberedWindowAtomicRawStepChecks (exact_ConcreteAtomicRoot exact_AtomicNoContextDescent)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparseRawTick (fallbackValue)
open NumberedWindowInternalSparsePathEnvelope (run nodeGood)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw encodeFrame)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape atSlot)
open NumberedWindowInternalLiteralAtomicRawGuardProof (freeTest bottomTest emitRawBottom freeCode bottomCode bottomAtRaw)
open NumberedWindowInternalFreshProbeDispatchProgram (compareNumbers)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo compareEvaluation)

def rootBottomComparison : Program 3 :=
  .composition compareNumbers (Fin.cons (.projection 2) (Fin.cons (onRaw emitRawBottom 0) Fin.elim0))

/-- The root's raw source is slot 0, and its original destination is
slot 2. The tests do not change its original witness payload. -/
def atomicRoot (p : Program 3) : Program 3 :=
  branch (onRaw freeTest 0) (branch (onRaw bottomTest 0) p (constantZero 3))
    (conjunction p rootBottomComparison)

/-- No actual context frame descends through a raw free or bottom atom.
Putting the tests on the actual fallback makes this available at each
iterated frame, not just on the outermost five-slot check. -/
def atomicFallback (p : Program 3) : Program 3 :=
  branch (onRaw freeTest 0) (branch (onRaw bottomTest 0) p (constantZero 3)) (constantZero 3)

private theorem bit (p : Program 1) (n : Nat) (q : Nat) :
    run (nodeGood p n) q = 0 ∨ run (nodeGood p n) q = 1 := by
  unfold run nodeGood
  rw [actualConjunctionEvaluation]
  split <;> simp

private theorem onSourceValue (p : Program 1) (q w r : Nat) :
    evaluate (onRaw p 0) (tape q w r) = run p q := by
  rw [atSlot]
  rfl

private theorem cmpValue (t n w r : Nat) :
    evaluate rootBottomComparison (tape (freeRaw t n) w r) =
      if r = bottomRaw t then 1 else 0 := by
  rw [rootBottomComparison,compositeTwo,onSourceValue]
  change evaluate compareNumbers (r ::ᵥ run emitRawBottom (freeRaw t n) ::ᵥ nil) = _
  change evaluate compareNumbers (r ::ᵥ run emitRawBottom (packNode 0 [t,n]) ::ᵥ nil) = _
  rw [bottomAtRaw 0 t [n]]
  exact compareEvaluation r (bottomRaw t)

theorem exact_LiteralAtomicRootCalibration (xs : Entries) (s : Settings) (p : Program 3)
    (fit : ActualRoot (root xs s) p) : ActualRoot (root xs s) (atomicRoot p) := by
  intro q w r
  change evaluate (atomicRoot p) (tape q w r) = _
  rw [atomicRoot,evalBranch,onSourceValue]
  rcases bit _ 2 q with f₀ | f₁
  · change run freeTest q = 0 at f₀
    rw [if_pos f₀,evalBranch,onSourceValue]
    rcases bit _ 1 q with b₀ | b₁
    · change run bottomTest q = 0 at b₀
      rw [if_pos b₀]
      exact fit q w r
    · change run bottomTest q = 1 at b₁
      obtain ⟨t,rfl⟩ := (bottomCode q).mp b₁
      rw [if_neg (by rw [b₁]; decide),exact_ConcreteAtomicRoot.2 xs s t w r]
      rfl
  · change run freeTest q = 1 at f₁
    obtain ⟨t,n,rfl⟩ := (freeCode q).mp f₁
    rw [if_neg (by rw [f₁]; decide),actualConjunctionEvaluation,fit (freeRaw t n) w r,cmpValue]
    cases h : root xs s (freeRaw t n) w r with
    | false => simp
    | true =>
      have target := (exact_ConcreteAtomicRoot.1 xs s t n w r h).1
      simp [target]

private theorem freeFallback (t n w r : Nat) : fallbackValue (freeRaw t n) w r = none := by
  unfold fallbackValue
  cases hx : unpackNode w with
  | none => rfl
  | some p => exact exact_AtomicNoContextDescent.1 p.1 p.2 t n r

private theorem bottomFallback (t w r : Nat) : fallbackValue (bottomRaw t) w r = none := by
  unfold fallbackValue
  cases hx : unpackNode w with
  | none => rfl
  | some p => exact exact_AtomicNoContextDescent.2 p.1 p.2 t r

theorem exact_LiteralAtomicFallbackCalibration (p : Program 3) (fit : ActualFallback p) :
    ActualFallback (atomicFallback p) := by
  intro q w r
  change evaluate (atomicFallback p) (tape q w r) = _
  rw [atomicFallback,evalBranch,onSourceValue]
  rcases bit _ 2 q with f₀ | f₁
  · change run freeTest q = 0 at f₀
    rw [if_pos f₀,evalBranch,onSourceValue]
    rcases bit _ 1 q with b₀ | b₁
    · change run bottomTest q = 0 at b₀
      rw [if_pos b₀]
      exact fit q w r
    · change run bottomTest q = 1 at b₁
      obtain ⟨t,rfl⟩ := (bottomCode q).mp b₁
      rw [if_neg (by rw [b₁]; decide),bottomFallback]
      rfl
  · change run freeTest q = 1 at f₁
    obtain ⟨t,n,rfl⟩ := (freeCode q).mp f₁
    rw [if_neg (by rw [f₁]; decide),freeFallback]
    rfl

#print axioms exact_LiteralAtomicRootCalibration
#print axioms exact_LiteralAtomicFallbackCalibration
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTickNumericProof
