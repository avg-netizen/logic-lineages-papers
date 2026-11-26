module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastHeaderInvarianceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastGuardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastGuardProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch constantZero)
open InternalAcceptanceCalibrationProof (evalBranch)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration packedLeast encodeState)
open NumberedWindowInternalFreshProbeDispatchProgram (predOne compareNumbers)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (compositeOne compositeTwo predEvaluation compareEvaluation)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (pairFirst outRaw pairSecond)
open NumberedWindowInternalLiteralLeastHeaderInvarianceProof (exact_LiteralPackedLeastCellHead)
open NumberedWindowScalarAlgorithm (Settings)

def inputHead : Program 2 := pairFirst cellHead
def outputHead : Program 2 := .composition cellHead (Fin.cons outRaw Fin.elim0)
def sameHeader : Program 2 :=
  .composition compareNumbers (Fin.cons inputHead (Fin.cons outputHead Fin.elim0))
def allowedOutput : Program 2 := branch sameHeader (constantZero 2) (.projection 1)

/-- New actual choice of packed least program: its input top tag and
the decoded output top tag are tested on the same real two-slot
report. Output zero remains the original failure element. -/
def headerLeast (L : Program 3) : Program 3 :=
  .composition allowedOutput (Fin.cons (.projection 2) (Fin.cons L Fin.elim0))

theorem checkHeaderValue (q coded : Nat) :
    evaluate sameHeader (q ::ᵥ coded ::ᵥ nil) =
      if run cellHead q = run cellHead coded.pred then 1 else 0 := by
  rw [sameHeader,compositeTwo,inputHead,pairFirst,outputHead,compositeOne,compositeOne,
    outRaw,pairSecond,compositeOne]
  have stored : evaluate (.projection (1 : Fin 2)) (q ::ᵥ coded ::ᵥ nil) = coded := rfl
  rw [stored,predEvaluation]
  exact compareEvaluation (run cellHead q) (run cellHead coded.pred)

theorem outputValue (q coded : Nat) :
    evaluate allowedOutput (q ::ᵥ coded ::ᵥ nil) =
      if run cellHead q = run cellHead coded.pred then coded else 0 := by
  have get : evaluate (.projection (1 : Fin 2)) (q ::ᵥ coded ::ᵥ nil) = coded := rfl
  have zero : evaluate (constantZero 2) (q ::ᵥ coded ::ᵥ nil) = 0 := rfl
  rw [allowedOutput,evalBranch,checkHeaderValue,get,zero]
  split <;> simp

/-- Full numerical preservation for every accepted or rejected packed
least query. The additional top tag equality will be used only on
the physically selected wrapper, never as a new object axiom. -/
theorem exact_LiteralHeaderLeast (s : Settings) (L : Program 3)
    (cal : ActualLeastCalibration s L) : ActualLeastCalibration s (headerLeast L) := by
  intro ctx ty q
  rw [headerLeast,compositeTwo,cal ctx ty q]
  change evaluate allowedOutput (q ::ᵥ encodeState (packedLeast s ctx ty q) ::ᵥ nil) = _
  rw [outputValue]
  cases actual : packedLeast s ctx ty q with
  | none => simp [encodeState]
  | some k =>
    have eq := exact_LiteralPackedLeastCellHead s ctx ty q k actual
    change (if run cellHead q = run cellHead k then k+1 else 0) = k+1
    simp [eq]

#print axioms exact_LiteralHeaderLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastGuardProof
