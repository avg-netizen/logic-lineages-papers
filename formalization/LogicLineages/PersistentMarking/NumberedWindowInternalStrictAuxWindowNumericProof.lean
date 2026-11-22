module

public import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowMemoChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open InternalAcceptance (constantZero)
open InternalRawListRecursion (lookup)
open InternalLessThanEvaluationProof (exactLessThanEvaluation)
open InternalEqualityTestEvaluationProof (exactSubtractionEvaluation exactEqualityEvaluation)
open NumberedWindowScalarAlgorithm (Settings admitted)
open NumberedWindowLexicalAlgorithm (typed)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowInternalSparseTypedRawTargets (packedWindow)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowRawExchangeVerticesCodecProof (nodeBounds)
open NumberedWindowInternalSparsePairEvaluationProof (consValue)
open NumberedWindowInternalSparsePathEnvelope (run field nodeGood)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termOne termFields)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorOne vectorTwo compositeThree)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (unaryValue binaryValue conjunctionOne)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck childAt earlierAt certain measureAt offsetAt)
open NumberedWindowInternalAuxWindowMemoTargets
open NumberedWindowInternalAuxWindowMemoChecks (exact_IntrinsicAuxWindow exact_PackedIntrinsicProjection)
open NumberedWindowInternalAuxWindowStepTargets
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalStrictAuxWindowTargets

private abbrev tape (i old ctx : Nat) : List.Vector Nat 4 := i ::ᵥ old ::ᵥ ctx ::ᵥ 0 ::ᵥ nil

private theorem current (i old ctx : Nat) : evaluate currentKey (tape i old ctx) = i+1 := by
  rw [currentKey,unaryValue]
  rfl

private theorem shape (i old ctx : Nat) : evaluate shapeCheck (tape i old ctx) = 1 ↔
    ∃ dom cod fn arg, unpackNode (i+1) = some (6,[dom,cod,fn,arg]) := by
  rw [shapeCheck,unaryValue,current,termOne]

private theorem fieldValue (i old ctx slot n : Nat) (fieldRead : run (field slot) (i+1) = n) :
    evaluate (childAt slot) (tape i old ctx) = n := by
  rw [childAt,unaryValue,current]
  exact fieldRead

private theorem earlier (i old ctx slot n : Nat) (read : evaluate (childAt slot) (tape i old ctx) = n)
    (bound : n < i+1) : evaluate (earlierAt slot) (tape i old ctx) = 1 := by
  rw [earlierAt,binaryValue,read,current,exactLessThanEvaluation,if_pos bound]

private theorem rowReport (i old ctx slot n : Nat) (read : evaluate (childAt slot) (tape i old ctx) = n) :
    evaluate (measureAt slot) (tape i old ctx) = evaluate lookup ((i-n) ::ᵥ old ::ᵥ nil) := by
  rw [measureAt,binaryValue,offsetAt,binaryValue,read]
  change evaluate lookup (evaluate InternalEqualityTest.subtract (n ::ᵥ i ::ᵥ nil) ::ᵥ old ::ᵥ nil) = _
  rw [exactSubtractionEvaluation]

private theorem guardOne (s : Settings) (T : Program 1) (cal : TypeGuardCalibrated s T)
    (i old ctx slot n : Nat) (read : evaluate (childAt slot) (tape i old ctx) = n) :
    evaluate (NumberedWindowInternalAuxExchangeMemoStepTargets.unaryAfter T (childAt slot)) (tape i old ctx) = 1 ↔
      typeGuard s n = true := by
  rw [unaryValue,read,cal]
  cases typeGuard s n <;> decide

private theorem agrees (slot : Nat) (code : Program 4) (xs : List.Vector Nat 4) :
    evaluate (reportTest slot code) xs = 1 ↔ evaluate (measureAt slot) xs = evaluate code xs := by
  rw [reportTest,binaryValue,exactEqualityEvaluation]
  split <;> simp_all

private theorem rightType (i old ctx dom cod : Nat)
    (d : evaluate (childAt 0) (tape i old ctx) = dom) (c : evaluate (childAt 1) (tape i old ctx) = cod) :
    evaluate functionCode (tape i old ctx) = arrow dom cod + 1 := by
  rw [functionCode,unaryValue,binaryValue,d,c,consValue]
  rfl

private theorem ownType (slot i old ctx ty : Nat) (r : evaluate (childAt slot) (tape i old ctx) = ty) :
    evaluate (NumberedWindowInternalAuxExchangeMemoStepTargets.unaryAfter .succ (childAt slot))
      (tape i old ctx) = ty+1 := by
  rw [unaryValue,r]
  rfl

theorem exact_StrictAuxWindowStepCalibration : ExactStrictAuxWindowStepCalibration := by
  intro s base T baseCal cal i old ctx previous
  change evaluate (strictAuxUpdate base T) (tape i old ctx) = intrinsicWindow s ctx (i+1)
  rw [strictAuxUpdate,evalBranch]
  by_cases hit : ∃ dom cod fn arg, unpackNode (i+1) = some (6,[dom,cod,fn,arg])
  · obtain ⟨dom,cod,fn,arg,read⟩ := hit
    have fs := termFields read
    have d := fieldValue i old ctx 0 dom fs.1
    have c := fieldValue i old ctx 1 cod fs.2.1
    have fnCode := fieldValue i old ctx 2 fn fs.2.2.1
    have argCode := fieldValue i old ctx 3 arg fs.2.2.2
    have smallFn := (nodeBounds read).2 fn (by simp)
    have smallArg := (nodeBounds read).2 arg (by simp)
    have header := (shape i old ctx).mpr ⟨dom,cod,fn,arg,read⟩
    have shapeEarlier : evaluate certain (tape i old ctx) = 1 := by
      simp only [certain,conjunctionOne]
      exact ⟨header,earlier i old ctx 2 fn fnCode smallFn,earlier i old ctx 3 arg argCode smallArg⟩
    let good := typeGuard s dom = true ∧ typeGuard s cod = true ∧
      intrinsicWindow s ctx fn = arrow dom cod + 1 ∧ intrinsicWindow s ctx arg = dom+1
    have bits : evaluate (admittedChildren T) (tape i old ctx) = 1 ↔ good := by
      simp only [good,admittedChildren,conjunctionOne,guardOne s T cal i old ctx 0 dom d,
        guardOne s T cal i old ctx 1 cod c,agrees,rowReport i old ctx 2 fn fnCode,
        rowReport i old ctx 3 arg argCode,previous fn smallFn,previous arg smallArg,
        rightType i old ctx dom cod d c,argumentCode,ownType 0 i old ctx dom d]
    have sourceGood :
        (typeGuard s dom && typeGuard s cod &&
          (intrinsicWindow s ctx fn == arrow dom cod + 1) && (intrinsicWindow s ctx arg == dom+1)) = true ↔
          good := by
      simp only [good,Bool.and_eq_true,beq_iff_eq,and_assoc]
    have intrinsic : intrinsicWindow s ctx (i+1) =
        (if (typeGuard s dom && typeGuard s cod &&
          (intrinsicWindow s ctx fn == arrow dom cod+1) && (intrinsicWindow s ctx arg == dom+1))
        then cod+1 else 0) := by
      rw [codeOfNode read]
      exact exact_IntrinsicAuxWindow s ctx dom cod fn arg
    rw [header,if_neg (by decide),strictAuxPositive,evalBranch,actualConjunctionEvaluation,
      shapeEarlier,resultCode,ownType 1 i old ctx cod c,intrinsic]
    by_cases success : good
    · rw [if_pos (sourceGood.mpr success),if_pos (And.intro (rfl : (1 : Nat) = 1) (bits.mpr success)),
        if_neg (show (1 : Nat) ≠ 0 from by decide)]
    · have reject := fun h : evaluate (admittedChildren T) (tape i old ctx) = 1 => success (bits.mp h)
      have rejected : ¬ (typeGuard s dom && typeGuard s cod &&
          (intrinsicWindow s ctx fn == arrow dom cod+1) && (intrinsicWindow s ctx arg == dom+1)) :=
        fun h => success (sourceGood.mp h)
      have conjunctionReject : ¬ ((1 : Nat) = 1 ∧
          evaluate (admittedChildren T) (tape i old ctx) = 1) := fun h => reject h.2
      rw [if_neg rejected,if_neg conjunctionReject,if_pos (show (0 : Nat) = 0 from rfl)] <;> rfl
  · have absent : evaluate shapeCheck (tape i old ctx) ≠ 1 :=
      fun h => hit ((shape i old ctx).mp h)
    have zero : evaluate shapeCheck (tape i old ctx) = 0 := by
      have bit : evaluate shapeCheck (tape i old ctx) = 0 ∨ evaluate shapeCheck (tape i old ctx) = 1 := by
        rw [shapeCheck,unaryValue]
        unfold termShape nodeGood run
        rw [actualConjunctionEvaluation]
        split <;> simp
      exact bit.resolve_right absent
    rw [zero,if_pos rfl,binaryValue,current]
    exact baseCal ctx (i+1)

private theorem rawZero (s : Settings) (ctx : Nat) : intrinsicWindow s ctx 0 = 0 := by
  have noSyntax : (syntaxBits 0).1 = false := rfl
  cases dec : unpack ctx <;> simp [intrinsicWindow,packedWindow,dec,admitted,typed,noSyntax]

private theorem selectedRow (s : Settings) (base : Program 2) (T : Program 1)
    (baseCal : IntrinsicWindowCalibrated s base) (cal : TypeGuardCalibrated s T) (ctx n : Nat) :
    evaluate (scratchRow (constantZero 2) (strictAuxUpdate base T)) (n ::ᵥ ctx ::ᵥ 0 ::ᵥ nil) =
      intrinsicWindow s ctx n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rw [rowZero,rawZero] <;> rfl
    | succ i =>
      rw [rowSucc]
      apply exact_StrictAuxWindowStepCalibration s base T baseCal cal
      intro n small
      rw [lookupAt (constantZero 2) (strictAuxUpdate base T) (ctx ::ᵥ 0 ::ᵥ nil) i n (Nat.le_of_lt_succ small)]
      exact ih n small

theorem exact_StrictAuxIntrinsicCalibration : ExactStrictAuxIntrinsicCalibration := by
  intro s base T baseCal cal ctx n
  unfold strictAuxIntrinsic
  rw [selectedIntrinsic,compositeThree]
  exact selectedRow s base T baseCal cal ctx n

private theorem queryEval (F : Program 2) (ctx ty raw : Nat) :
    evaluate (intrinsicQuery F) (ctx ::ᵥ ty ::ᵥ raw ::ᵥ nil) =
      if evaluate F (ctx ::ᵥ raw ::ᵥ nil) = ty+1 then 1 else 0 := by
  let xs := ctx ::ᵥ ty ::ᵥ raw ::ᵥ nil
  change evaluate InternalEqualityTest.equalityTest
    (List.Vector.ofFn fun i => evaluate ((![.composition F ![.projection 0,.projection 2],
      .composition .succ ![.projection 1]] : Fin 2 → Program 3) i) xs) = _
  rw [vectorTwo]
  change evaluate InternalEqualityTest.equalityTest
    (evaluate F (List.Vector.ofFn fun i => evaluate ((![.projection 0,.projection 2] : Fin 2 → Program 3) i) xs) ::ᵥ
      evaluate Program.succ (List.Vector.ofFn fun i => evaluate ((![.projection 1] : Fin 1 → Program 3) i) xs) ::ᵥ nil) = _
  rw [vectorTwo,vectorOne]
  exact exactEqualityEvaluation (evaluate F (ctx ::ᵥ raw ::ᵥ nil)) (ty+1)

theorem exact_StrictAuxWindowCalibration : ExactStrictAuxWindowCalibration := by
  intro s base T baseCal cal ctx ty raw
  unfold strictAuxWindow
  rw [queryEval,exact_StrictAuxIntrinsicCalibration s base T baseCal cal ctx raw,exact_PackedIntrinsicProjection]
  by_cases yes : intrinsicWindow s ctx raw = ty+1
  · simp [yes]
  · have no : (intrinsicWindow s ctx raw == ty+1) = false := by
      apply Bool.eq_false_iff.mpr
      intro found
      exact yes (beq_iff_eq.mp found)
    rw [if_neg yes,no]
    rfl

#print axioms exact_StrictAuxWindowStepCalibration
#print axioms exact_StrictAuxIntrinsicCalibration
#print axioms exact_StrictAuxWindowCalibration

end LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowNumericProof
