module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineExchangeRankProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptance (constantZero)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThan (constantOne)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
  (evalBranch actualConjunctionEvaluation)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
  (exactPredecessorEvaluation exactEqualityEvaluation)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorOne compositeTwo)
open NumberedWindowInternalRankCheckedLeast
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration packedLeast encodeState)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowScalarAlgorithm (Settings least)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowNeutralSpinePositiveRankProof (exact_OriginalNeutralRankLeast)
open NumberedWindowNeutralSpineExchangeRankProof (exact_OriginalKeepsNeutralRank)

private theorem evalUnaryOn (g : Program 1) (p : Program 3) (xs : List.Vector Nat 3) :
    evaluate (unaryOn g p) xs = evaluate g (evaluate p xs ::ᵥ nil) := by
  unfold unaryOn
  change evaluate g (List.Vector.ofFn (fun _ : Fin 1 => evaluate p xs)) = _
  rw [vectorOne]

private theorem successRankTest (g : Program 1) (L : Program 3)
    (ctx ty q k : Nat)
    (old : evaluate L (ctx ::ᵥ ty ::ᵥ q ::ᵥ nil) = k+1)
    (same : evaluate g (q ::ᵥ nil) = evaluate g (k ::ᵥ nil)) :
    evaluate (rankTest g L) (ctx ::ᵥ ty ::ᵥ q ::ᵥ nil) = 1 := by
  let tape := ctx ::ᵥ ty ::ᵥ q ::ᵥ nil
  have seed : evaluate (seedRank g) tape = evaluate g (q ::ᵥ nil) := by
    rw [seedRank,evalUnaryOn]
    rfl
  have out : evaluate (outputRank g L) tape = evaluate g (k ::ᵥ nil) := by
    rw [outputRank,evalUnaryOn,evalUnaryOn,old,exactPredecessorEvaluation,Nat.pred_succ]
  have bit : evaluate (rankEq g L) tape = 1 := by
    rw [rankEq,compositeTwo,seed,out,same,exactEqualityEvaluation]
    simp
  rw [rankTest,actualConjunctionEvaluation]
  change (if evaluate (rankEq g L) tape = 1 ∧ evaluate (constantOne 3) tape = 1 then 1 else 0) = _
  rw [bit]
  have one : evaluate (constantOne 3) tape = 1 := by simp [constantOne,constantZero,evaluate]
  simp [one]

/-- Exact same original numeric answer at every input. The new
arithmetic equality check is conservative by original class-round rank
preservation and the genuinely chosen raw rank program. -/
theorem exact_OriginalRankCheckedLeastNumeric (s : Settings) (raw : Program 1) (L : Program 3)
    (rFit : ∀ n, evaluate raw (n ::ᵥ nil) = rawRank n)
    (lFit : ActualLeastCalibration s L) :
    ActualLeastCalibration s (checkedLeast raw L) := by
  intro ctx ty q
  let tape := ctx ::ᵥ ty ::ᵥ q ::ᵥ nil
  have old := lFit ctx ty q
  unfold checkedLeast
  rw [evalBranch]
  cases report : packedLeast s ctx ty q with
  | none =>
    have noResult : evaluate L tape = 0 := by
      simpa [report,encodeState] using old
    simp only [tape] at noResult
    rw [noResult]
    change (if _ then 0 else 0) = _
    simp [report,encodeState]
  | some k =>
    have yes : evaluate L tape = k+1 := by
      simpa [report,encodeState] using old
    obtain ⟨Γ,original⟩ : ∃ Γ, least s Γ ty q = some k := by
      cases known : unpack ctx with
      | none => simp [packedLeast,known] at report
      | some Γ =>
        exact ⟨Γ,by simpa [packedLeast,known] using report⟩
    have preserved := exact_OriginalNeutralRankLeast s (exact_OriginalKeepsNeutralRank s) Γ ty q k original
    have same : evaluate raw (q ::ᵥ nil) = evaluate raw (k ::ᵥ nil) := by
      rw [rFit,rFit,← preserved]
    rw [successRankTest raw L ctx ty q k yes same,if_neg (by decide : (1 : Nat) ≠ 0)]
    exact yes

#print axioms exact_OriginalRankCheckedLeastNumeric
end LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastNumericProof
