module

public import LogicLineages.PersistentMarking.NumberedWindowInternalTransparentAuxRankTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalTransparentAuxRankNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero conjunction)
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open InternalLessThanEvaluationProof (exactLessThanEvaluation)
open InternalEqualityTestEvaluationProof (exactSubtractionEvaluation)
open InternalRawListRecursion (lookup)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank next table row tableEarlier)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowInternalSparsePathEnvelope (run field)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter currentKey)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (args unaryValue binaryValue conjunctionOne)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck childAt earlierAt measureAt offsetAt)
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeThree)
open NumberedWindowRawExchangeVerticesCodecProof (nodeBounds)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termOne termFields)

open NumberedWindowInternalTransparentAuxRankTargets

private theorem current (i old : Nat) : evaluate currentKey (args i old) = i+1 := by
  rw [currentKey,unaryValue] <;> rfl

theorem exact_OriginalAuxRankValue (raw dom cod fn arg : Nat)
    (read : unpackNode raw = some (6,[dom,cod,fn,arg])) :
    fn < raw ∧ rawRank raw = (if rawRank fn = 0 then 0 else rawRank fn + 1) := by
  have small := (nodeBounds read).2 fn (by simp)
  have source : row (table raw) 6 [dom,cod,fn,arg] =
    (if (table raw).getD fn 0 = 0 then 0 else (table raw).getD fn 0 + 1) := rfl
  refine ⟨small,?_⟩
  rw [rawRank,next,read,Option.map_some,Option.getD_some,source,tableEarlier fn raw small]

theorem exact_OriginalAuxRankZeroIff (raw dom cod fn arg : Nat)
    (read : unpackNode raw = some (6,[dom,cod,fn,arg])) :
    rawRank raw = 0 ↔ rawRank fn = 0 := by
  rw [(exact_OriginalAuxRankValue raw dom cod fn arg read).2]
  by_cases z : rawRank fn = 0 <;> simp [z]

private theorem shape (i old : Nat) : evaluate shapeCheck (args i old) = 1 ↔
    ∃ dom cod fn arg, unpackNode (i+1) = some (6,[dom,cod,fn,arg]) := by
  rw [shapeCheck,unaryValue,current,termOne]

private theorem selectField (j i old value : Nat)
    (found : run (field j) (i+1) = value) : evaluate (childAt j) (args i old) = value := by
  rw [childAt,unaryValue,current]
  exact found

private theorem lookupValue (slot i old q : Nat)
    (selected : evaluate (childAt slot) (args i old) = q) :
    evaluate (measureAt slot) (args i old) = evaluate lookup ((i-q) ::ᵥ old ::ᵥ nil) := by
  rw [measureAt,binaryValue,offsetAt,binaryValue,selected]
  change evaluate lookup (evaluate InternalEqualityTest.subtract (q ::ᵥ i ::ᵥ nil) ::ᵥ old ::ᵥ nil) = _
  rw [exactSubtractionEvaluation]

private theorem earlier (slot i old v : Nat) (selected : evaluate (childAt slot) (args i old) = v)
    (small : v < i+1) : evaluate (earlierAt slot) (args i old) = 1 := by
  rw [earlierAt,binaryValue,selected,current,exactLessThanEvaluation,if_pos small]

theorem exact_TransparentAuxRankUpdateCalibration (g : Program 1) (fit : RankCalibrated g)
    (i old : Nat)
    (previous : ∀ n, n < i+1 → evaluate lookup ((i-n) ::ᵥ old ::ᵥ nil) = rawRank n) :
    evaluate (rankUpdate g) (args i old) = rawRank (i+1) := by
  rw [rankUpdate,evalBranch]
  by_cases aux : ∃ dom cod fn arg, unpackNode (i+1) = some (6,[dom,cod,fn,arg])
  · obtain ⟨dom,cod,fn,arg,read⟩ := aux
    obtain ⟨small,value⟩ := exact_OriginalAuxRankValue (i+1) dom cod fn arg read
    have selected := selectField 2 i old fn (termFields read).2.2.1
    have guard : evaluate rankGuard (args i old) = 1 := by
      simp only [rankGuard,conjunctionOne]
      exact ⟨(shape i old).mpr ⟨dom,cod,fn,arg,read⟩,earlier 2 i old fn selected small⟩
    have fnValue : evaluate (measureAt 2) (args i old) = rawRank fn :=
      (lookupValue 2 i old fn selected).trans (previous fn small)
    have succValue : evaluate (unaryAfter .succ (measureAt 2)) (args i old) = rawRank fn + 1 := by
      rw [unaryValue,fnValue] <;> rfl
    rw [guard,if_neg (by decide),rankAtFn,evalBranch,fnValue,succValue,value] <;>
      (by_cases z : rawRank fn = 0 <;> simp only [z,if_true,if_false] <;> rfl)
  · have miss : evaluate shapeCheck (args i old) ≠ 1 := fun pass => aux ((shape i old).mp pass)
    have guard : evaluate rankGuard (args i old) = 0 := by
      rw [rankGuard,actualConjunctionEvaluation]
      simp [miss]
    rw [guard,if_pos rfl,unaryValue,current]
    exact fit (i+1)

private theorem selectedRow (g : Program 1) (fit : RankCalibrated g) (n : Nat) :
    evaluate (scratchRow (constantZero 2) (rankUpdate g)) (n ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) =
      rawRank n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rw [rowZero]; rfl
    | succ i =>
      let old := evaluate (scratchTable (constantZero 2) (rankUpdate g)) (i ::ᵥ 0 ::ᵥ 0 ::ᵥ nil)
      have prior : ∀ child, child < i+1 →
          evaluate lookup ((i-child) ::ᵥ old ::ᵥ nil) = rawRank child := by
        intro child small
        change evaluate lookup ((i-child) ::ᵥ
          evaluate (scratchTable (constantZero 2) (rankUpdate g)) (i ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) ::ᵥ nil) =
          rawRank child
        exact (lookupAt (constantZero 2) (rankUpdate g) (0 ::ᵥ 0 ::ᵥ nil)
          i child (Nat.le_of_lt_succ small)).trans (ih child small)
      have step : evaluate (rankUpdate g) (args i old) = rawRank (i+1) :=
        exact_TransparentAuxRankUpdateCalibration g fit i old prior
      have unfoldRow : evaluate (scratchRow (constantZero 2) (rankUpdate g)) ((i+1) ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) =
          evaluate (rankUpdate g) (args i old) :=
        rowSucc (constantZero 2) (rankUpdate g) (0 ::ᵥ 0 ::ᵥ nil) i
      exact unfoldRow.trans step

theorem exact_TransparentAuxRankCalibration (g : Program 1) (fit : RankCalibrated g) :
    RankCalibrated (auxRank g) := by
  intro n
  change run (auxRank g) n = rawRank n
  unfold auxRank run
  rw [selectedMeasure,compositeThree]
  exact selectedRow g fit n

#print axioms exact_OriginalAuxRankValue
#print axioms exact_OriginalAuxRankZeroIff
#print axioms exact_TransparentAuxRankUpdateCalibration
#print axioms exact_TransparentAuxRankCalibration

end LogicLineages.PersistentMarking.NumberedWindowInternalTransparentAuxRankNumericProof
