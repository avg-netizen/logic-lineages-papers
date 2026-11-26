module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoNumericStepProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoCalibrationProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptance (constantZero)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowExchangeAlgorithm (bits)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseScalarEdge (exchangeTape)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorTwo vectorThree compositeTwo compositeThree)
open NumberedWindowInternalSparsePairEvaluationProof (pairValue)
open NumberedWindowInternalLiteralTypedContextMemoProof (selectedContextMemo contextualPair)
open NumberedWindowInternalLiteralBiAuxRawMemoStageProof (rawAuxMemoStage)
open NumberedWindowInternalLiteralBiAuxRawMemoOpenProof (biAuxRawMemo)
open NumberedWindowInternalLiteralBiAuxRawMemoNumericStepProof (exact_LiteralBiAuxRawMemoStep)

private theorem rawMemoRow (s : Settings) (X : Program 2) (V : Program 1)
    (fit : ActualTermExchange s X) (valid : TermSyntaxCalibrated V) (key : Nat) :
    ∀ a b, key = pair a b →
    evaluate (scratchRow (constantZero 2) (rawAuxMemoStage X V)) (key ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) =
      ((bits s.equivalentHeads a b).1).toNat := by
  induction key using Nat.strongRecOn with
  | ind key ih =>
    intro a b code
    cases key with
    | zero =>
      rw [rowZero]
      have atZero : a = 0 := by unfold pair at code; omega
      have no : (syntaxBits 0).1 = false := rfl
      simp [bits,atZero,no]
      rfl
    | succ i =>
      rw [rowSucc]
      apply exact_LiteralBiAuxRawMemoStep s X V fit valid i _ a b code
      intro p q earlier
      rw [lookupAt (constantZero 2) (rawAuxMemoStage X V) (0 ::ᵥ 0 ::ᵥ nil)
        i (pair p q) (Nat.le_of_lt_succ earlier)]
      exact ih (pair p q) earlier p q rfl

/-- The selected raw memo checks the original binary term exchange on
every pair of natural inputs, including the rejected zero and malformed
codes. No symmetry assumption is needed for this directed calibration. -/
theorem exact_LiteralBiAuxRawMemo (s : Settings) (X : Program 2) (V : Program 1)
    (fit : ActualTermExchange s X) (valid : TermSyntaxCalibrated V) :
    ActualTermExchange s (biAuxRawMemo X V) := by
  intro a b
  have first : exchangeTape a b 0 = a := rfl
  have second : exchangeTape a b 1 = b := rfl
  rw [vectorTwo,first,second]
  let ps : Fin 3 → Program 2 := ![constantZero 2,.projection 0,.projection 1]
  change evaluate (selectedContextMemo (rawAuxMemoStage X V))
    (List.Vector.ofFn (fun j => evaluate (ps j) (a ::ᵥ b ::ᵥ nil))) = _
  rw [vectorThree]
  change evaluate (selectedContextMemo (rawAuxMemoStage X V)) (0 ::ᵥ a ::ᵥ b ::ᵥ nil) = _
  rw [selectedContextMemo,compositeThree,contextualPair,compositeTwo]
  change evaluate (scratchRow (constantZero 2) (rawAuxMemoStage X V))
    (evaluate NumberedWindowInternalSparsePair.pair (a ::ᵥ b ::ᵥ nil) ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) = _
  rw [pairValue]
  exact rawMemoRow s X V fit valid (pair a b) a b rfl

#print axioms exact_LiteralBiAuxRawMemo
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoCalibrationProof
