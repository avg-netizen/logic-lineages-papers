module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoStageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoEvaluationProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalEqualityTestEvaluationProof (exactSubtractionEvaluation)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (cellAt headTailOfCell)
open NumberedWindowInternalSparsePairEvaluationProof (pairValue consValue)
open NumberedWindowInternalSparseDirectedRoundsNumericTapeProof (vectorFour)
open NumberedWindowInternalSparseFieldParserRawPairProof (encodedPair)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeOne compositeTwo vectorOne)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (unaryValue binaryValue conjunctionOne)
open NumberedWindowInternalAuxExchangeMemoStepTargets (rawSource rawTarget currentKey packedKey)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowInternalLiteralTypedMemoStageProof
open NumberedWindowInternalLiteralTypedAuxEdgeGuardProof (readSlot)

abbrev tape (x y z w : Nat) : List.Vector Nat 4 := x ::ᵥ y ::ᵥ z ::ᵥ w ::ᵥ nil
def carrierCode (ctx old prev : Nat) : Nat := pair ctx (pair old (pair prev 0 + 1) + 1) + 1

theorem fourEval (p : Program 4) (parts : Fin 4 → Program 4) (xs : List.Vector Nat 4) :
    evaluate (.composition p parts) xs =
      evaluate p (tape (evaluate (parts 0) xs) (evaluate (parts 1) xs)
        (evaluate (parts 2) xs) (evaluate (parts 3) xs)) := by
  change evaluate p (List.Vector.ofFn _) = _
  rw [vectorFour]

theorem slotEval (P : Program 1) (j : Fin 4) (xs : List.Vector Nat 4) :
    evaluate (readSlot P j) xs = run P (xs.get j) := by
  rw [readSlot,compositeOne]
  rfl

private theorem afterEval (P Q : Program 1) (k : Nat) :
    run (after1 P Q) k = run P (run Q k) := by
  change evaluate P (List.Vector.ofFn (fun _ : Fin 1 => evaluate Q (k ::ᵥ nil))) = _
  rw [vectorOne]
  rfl

private theorem carrierReads (ctx old prev : Nat) :
    run holdContext (carrierCode ctx old prev) = ctx ∧ run holdTable (carrierCode ctx old prev) = old ∧
      run holdIndex (carrierCode ctx old prev) = prev := by
  let low := pair prev 0 + 1
  let rest := pair old low + 1
  have outer := headTailOfCell (cellAt ctx rest)
  have mid := headTailOfCell (cellAt old low)
  have last := headTailOfCell (cellAt prev 0)
  unfold carrierCode
  exact ⟨outer.1,
    by rw [holdTable,afterEval,outer.2]; exact mid.1,
    by rw [holdIndex,afterEval,afterEval,outer.2,mid.2]; exact last.1⟩

private theorem carrierEvaluates (ctx old prev : Nat) :
    evaluate memoCarrier (tape prev old ctx 0) = carrierCode ctx old prev := by
  unfold memoCarrier consOf
  rw [compositeTwo,compositeTwo,compositeTwo]
  change evaluate NumberedWindowInternalSparsePair.fieldCons (ctx ::ᵥ
    evaluate NumberedWindowInternalSparsePair.fieldCons (old ::ᵥ
      evaluate NumberedWindowInternalSparsePair.fieldCons (prev ::ᵥ 0 ::ᵥ nil) ::ᵥ nil) ::ᵥ nil) = _
  rw [consValue,consValue,consValue]
  rfl

theorem exact_LiteralTypedMemoStageTape (Base : Program 4) (ctx old prev a b : Nat)
    (key : prev + 1 = pair a b) :
    evaluate (typedMemoStage Base) (tape prev old ctx 0) =
      evaluate (stageGuard Base) (tape (carrierCode ctx old prev) 0 a b) := by
  let xs := tape prev old ctx 0
  have packed : evaluate packedKey xs = pair a b + 1 := by
    rw [packedKey,unaryValue,currentKey,unaryValue]
    change prev + 1 + 1 = _
    rw [key]
  have reads := headTailOfCell (cellAt a b)
  have l : evaluate rawSource xs = a := by rw [rawSource,unaryValue,packed]; exact reads.1
  have r : evaluate rawTarget xs = b := by rw [rawTarget,unaryValue,packed]; exact reads.2
  rw [typedMemoStage,fourEval]
  change evaluate (stageGuard Base) (tape (evaluate memoCarrier xs) 0
    (evaluate rawSource xs) (evaluate rawTarget xs)) = _
  rw [carrierEvaluates,l,r]

private theorem lookupEvaluation (ctx old prev ty q r : Nat) (i j : Fin 4) :
    let xs := tape (carrierCode ctx old prev) ty q r
    evaluate (lookupOnCarrier i j) xs =
      evaluate ID1Completion.InternalRawListRecursion.lookup
        ((prev - pair (xs.get i) (xs.get j)) ::ᵥ old ::ᵥ nil) := by
  let xs := tape (carrierCode ctx old prev) ty q r
  have facts := carrierReads ctx old prev
  change evaluate (lookupOnCarrier i j) xs = _
  unfold lookupOnCarrier
  dsimp only
  rw [binaryValue,binaryValue,binaryValue,slotEval,slotEval]
  change evaluate ID1Completion.InternalRawListRecursion.lookup
    (evaluate ID1Completion.InternalEqualityTest.subtract
      (evaluate NumberedWindowInternalSparsePair.pair (xs.get i ::ᵥ xs.get j ::ᵥ nil) ::ᵥ
        run holdIndex (carrierCode ctx old prev) ::ᵥ nil) ::ᵥ
      run holdTable (carrierCode ctx old prev) ::ᵥ nil) = _
  rw [facts.2.1,facts.2.2,pairValue,exactSubtractionEvaluation]

/-- All numeric carried computations are on the exact two index offsets,
not on a semantic reconstruction of what the scratch table should hold. -/
theorem exact_LiteralTypedMemoChildNumerals (Base : Program 4) (ctx old prev ty q r : Nat) :
    evaluate (childOnCarrier Base) (tape (carrierCode ctx old prev) ty q r) = 1 ↔
      evaluate Base (tape ctx ty q r) = 1 ∧
      evaluate ID1Completion.InternalRawListRecursion.lookup ((prev - pair q r) ::ᵥ old ::ᵥ nil) = 1 ∧
      evaluate ID1Completion.InternalRawListRecursion.lookup ((prev - pair r q) ::ᵥ old ::ᵥ nil) = 1 := by
  rw [childOnCarrier,conjunctionOne,conjunctionOne,
    lookupEvaluation ctx old prev ty q r 2 3,lookupEvaluation ctx old prev ty q r 3 2,
    baseOnCarrier,fourEval]
  change (evaluate Base (tape (evaluate (readSlot holdContext 0) _) ty q r) = 1 ∧ _) ↔ _
  rw [slotEval]
  change (evaluate Base (tape (run holdContext (carrierCode ctx old prev)) ty q r) = 1 ∧ _) ↔ _
  rw [(carrierReads ctx old prev).1]
  rfl

#print axioms exact_LiteralTypedMemoStageTape
#print axioms exact_LiteralTypedMemoChildNumerals
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoEvaluationProof
