module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoUnfoldingProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoEvaluationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoAuxNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryChecks
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoCalibrationProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open ID1Completion.InternalRawListRecursion (lookup)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowScalarAlgorithm (Settings edge admitted)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowLexicalAlgorithm (typed)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowRawExchangeSymmetryChecks (exact_ScalarEdgeSymmetry)
open NumberedWindowRawExchangeVerticesCodecProof (getFieldLt)
open NumberedWindowInternalSparsePathEnvelope (run nodeGood)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termOne)
open NumberedWindowInternalSparseScalarEdge (packedEdge)
open NumberedWindowInternalSparseDirectedRoundsTargets (exactEdgeBit)
open NumberedWindowInternalSparseDirectedRoundsNumericTapeProof (vectorFour)
open NumberedWindowInternalSparseDirectedSeen (edgeTape)
open NumberedWindowInternalSparsePairEvaluationProof (pairValue)
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (lookupAt rowSucc)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (conjunctionBit conjunctionOne)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo compositeThree)
open NumberedWindowInternalLiteralEdgeObserverFitProof (WholeEdgeFit)
open NumberedWindowInternalLiteralTypedAuxExchangeCasesProof (exact_LiteralTypedAuxExchangeCases)
open NumberedWindowInternalLiteralTypedContextMemoProof (selectedContextMemo contextualPair)
open NumberedWindowInternalLiteralTypedDualMemoProof (dualContextMemo orderedMemo)
open NumberedWindowInternalLiteralTypedMemoStageProof (typedMemoStage stageGuard childOnCarrier)
open NumberedWindowInternalLiteralTypedMemoEvaluationProof
open NumberedWindowInternalLiteralTypedMemoAuxNumericProof
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)

private theorem bitValue (s : Settings) (Base : Program 4) (fit : WholeEdgeFit s Base)
    (ctx ty q r : Nat) :
    evaluate Base (tape ctx ty q r) = 1 ↔ packedEdge s ctx ty q r = true := by
  have same : exactEdgeBit Base ctx ty q r = packedEdge s ctx ty q r :=
    congrFun (congrFun (congrFun (congrFun fit ctx) ty) q) r
  rw [exactEdgeBit,vectorFour] at same
  simpa [tape,edgeTape] using Iff.of_eq (congrArg (· = true) same)

private theorem related (s : Settings) {ctx ty q r : Nat} {g : List Nat}
    (scope : unpack ctx = some g) :
    packedEdge s ctx ty q r = true ↔ edge s g ty q r = true := by
  simp [packedEdge,scope]

private theorem pairSumBelow (x y a b : Nat) (small : x+y < a+b) : pair x y < pair a b := by
  let lo := x+y
  let hi := a+b
  have k : lo+1 ≤ hi := small
  have middle : (lo+1)*(lo+1) ≤ hi*hi := Nat.mul_le_mul k k
  have left : lo*lo + x < (lo+1)*(lo+1) := by
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul]
    dsimp [lo]
    omega
  change lo*lo+x < hi*hi+a
  exact Nat.lt_of_lt_of_le left (Nat.le_trans middle (Nat.le_add_right _ _))

private theorem pairBoth (x y a b : Nat) (l : x < a) (r : y < b) :
    pair x y < pair a b ∧ pair y x < pair a b :=
  ⟨pairSumBelow x y a b (by omega),pairSumBelow y x a b (by omega)⟩

private theorem impossibleZero (s : Settings) (ctx ty q r : Nat) (key : 0 = pair q r)
    (ok : packedEdge s ctx ty q r = true) : False := by
  have qzero : q = 0 := by unfold pair at key; omega
  subst q
  have no : (syntaxBits 0).1 = false := rfl
  cases parse : unpack ctx <;> simp [packedEdge,parse,edge,admitted,typed,no] at ok

/-- Only a positive-preservation theorem is needed for the memo. At any
input the original Base still decides the ordinary typed windows. This
induction uses both actual earlier rows for the actual retained child. -/
private theorem positiveRow (s : Settings) (Base : Program 4) (fit : WholeEdgeFit s Base)
    (symmetry : HeadPairsSymmetric s.equivalentHeads) (key : Nat) :
    ∀ ctx ty q r, key = pair q r → packedEdge s ctx ty q r = true →
      evaluate (scratchRow (constantZero 2) (typedMemoStage Base)) (key ::ᵥ ctx ::ᵥ 0 ::ᵥ nil) = 1 := by
  induction key using Nat.strongRecOn with
  | ind key ih =>
    intro ctx ty q r encoded ok
    cases key with
    | zero => exact False.elim (impossibleZero s ctx ty q r encoded ok)
    | succ prev =>
      let R := typedMemoStage Base
      let old := evaluate (scratchTable (constantZero 2) R) (prev ::ᵥ ctx ::ᵥ 0 ::ᵥ nil)
      rw [rowSucc]
      change evaluate R (tape prev old ctx 0) = 1
      rw [exact_LiteralTypedMemoStageTape Base ctx old prev q r encoded]
      cases parsed : unpack ctx with
      | none => simp [packedEdge,parsed] at ok
      | some g =>
        have top := (related s parsed).mp ok
        by_cases isAux : run termShape q = 1
        · obtain ⟨d,c,f,a,hq⟩ := (termOne q).mp isAux
          obtain ⟨_,f',a',hr,step⟩ := exact_LiteralTypedAuxExchangeCases s g ty q r d c f a top hq
          have next (T x y : Nat) (ar : edge s g T x y = true) (lx : x < q) (ly : y < r) :
              evaluate (childOnCarrier Base) (tape (carrierCode ctx old prev) T x y) = 1 := by
            have forward := (related s parsed).mpr ar
            have reverse := (related s parsed).mpr
              ((exact_ScalarEdgeSymmetry s symmetry g T x y).symm.trans ar)
            obtain ⟨fwd,rev⟩ := pairBoth x y q r lx ly
            rw [← encoded] at fwd rev
            apply (exact_LiteralTypedMemoChildNumerals Base ctx old prev T x y).mpr
            refine ⟨(bitValue s Base fit ctx T x y).mpr forward,?_,?_⟩
            · change evaluate lookup _ = 1
              unfold old
              rw [lookupAt (constantZero 2) R (ctx ::ᵥ 0 ::ᵥ nil) prev (pair x y) (Nat.le_of_lt_succ fwd)]
              exact ih (pair x y) fwd ctx T x y rfl forward
            · change evaluate lookup _ = 1
              unfold old
              rw [lookupAt (constantZero 2) R (ctx ::ᵥ 0 ::ᵥ nil) prev (pair y x) (Nat.le_of_lt_succ rev)]
              exact ih (pair y x) rev ctx T y x rfl reverse
          apply exact_LiteralAuxiliaryTypedStageAccept (childOnCarrier Base) (carrierCode ctx old prev)
            0 q r d c f a f' a' hq hr
          rcases step with fn | arg
          · exact Or.inl ⟨next (arrow d c) f f' fn.1 (getFieldLt hq 2) (getFieldLt hr 2),fn.2⟩
          · exact Or.inr ⟨arg.1,next d a a' arg.2 (getFieldLt hq 3) (getFieldLt hr 3)⟩
        · have zero : run termShape q = 0 := by
            have bit : run termShape q = 0 ∨ run termShape q = 1 := by
              unfold run termShape nodeGood
              exact conjunctionBit _ _ _
            exact bit.resolve_right isAux
          exact exact_LiteralNonAuxiliaryTypedStageAccept (childOnCarrier Base)
            (carrierCode ctx old prev) 0 q r zero

private theorem memoNumeral (R : Program 4) (ctx q r : Nat) :
    evaluate (selectedContextMemo R) (ctx ::ᵥ q ::ᵥ r ::ᵥ nil) =
      evaluate (scratchRow (constantZero 2) R) (pair q r ::ᵥ ctx ::ᵥ 0 ::ᵥ nil) := by
  rw [selectedContextMemo,compositeThree,contextualPair,compositeTwo]
  change evaluate (scratchRow (constantZero 2) R)
    (evaluate NumberedWindowInternalSparsePair.pair (q ::ᵥ r ::ᵥ nil) ::ᵥ ctx ::ᵥ 0 ::ᵥ nil) = _
  rw [pairValue]

/-- The concrete recursive typed memo is now fully calibrated against
the exact original finite-edge checker, for all original and malformed
inputs. Its separately checked open unfolding is proof-relevant. -/
theorem exact_WholeRecursiveTypedMemo (s : Settings) (Base : Program 4)
    (fit : WholeEdgeFit s Base) (symmetry : HeadPairsSymmetric s.equivalentHeads) :
    WholeEdgeFit s (recursiveTypedMemo Base) := by
  funext ctx ty q r
  unfold exactEdgeBit
  rw [vectorFour]
  change decide (evaluate (recursiveTypedMemo Base) (tape ctx ty q r) = 1) = packedEdge s ctx ty q r
  let R := typedMemoStage Base
  have forward : evaluate (orderedMemo R 2 3) (tape ctx ty q r) =
      evaluate (scratchRow (constantZero 2) R) (pair q r ::ᵥ ctx ::ᵥ 0 ::ᵥ nil) := by
    rw [orderedMemo,compositeThree]
    exact memoNumeral R ctx q r
  have reverse : evaluate (orderedMemo R 3 2) (tape ctx ty q r) =
      evaluate (scratchRow (constantZero 2) R) (pair r q ::ᵥ ctx ::ᵥ 0 ::ᵥ nil) := by
    rw [orderedMemo,compositeThree]
    exact memoNumeral R ctx r q
  have spec : evaluate (recursiveTypedMemo Base) (tape ctx ty q r) = 1 ↔
      packedEdge s ctx ty q r = true := by
    rw [recursiveTypedMemo,dualContextMemo,conjunctionOne,conjunctionOne,forward,reverse,
      bitValue s Base fit ctx ty q r]
    refine ⟨fun h => h.1,fun h => ⟨h,positiveRow s Base fit symmetry (pair q r) ctx ty q r rfl h,?_⟩⟩
    have back : packedEdge s ctx ty r q = true := by
      cases parsed : unpack ctx with
      | none => simp [packedEdge,parsed] at h
      | some g =>
        apply (related s parsed).mpr
        rw [← exact_ScalarEdgeSymmetry s symmetry g ty q r]
        exact (related s parsed).mp h
    exact positiveRow s Base fit symmetry (pair r q) ctx ty r q rfl back
  cases answer : packedEdge s ctx ty q r with
  | false => simp [answer] at spec; simp [spec]
  | true => simp [answer] at spec; simp [spec]

#print axioms exact_WholeRecursiveTypedMemo
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoCalibrationProof
