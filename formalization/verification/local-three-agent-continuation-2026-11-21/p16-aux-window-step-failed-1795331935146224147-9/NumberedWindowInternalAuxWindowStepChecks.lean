module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepPrograms
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowMemoChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open InternalLessThanEvaluationProof (exactLessThanEvaluation)
open InternalEqualityTestEvaluationProof (exactSubtractionEvaluation exactEqualityEvaluation)
open InternalRawListRecursion (lookup)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowRawExchangeVerticesCodecProof (nodeBounds)
open NumberedWindowInternalSparsePairEvaluationProof (consValue)
open NumberedWindowInternalSparsePathEnvelope (run field)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termOne termFields)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorOne vectorTwo)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (unaryValue binaryValue conjunctionOne)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck childAt earlierAt certain measureAt offsetAt)
open NumberedWindowInternalAuxWindowMemoTargets
open NumberedWindowInternalAuxWindowMemoChecks (exact_IntrinsicMemoCalibration exact_PackedIntrinsicProjection)
open NumberedWindowInternalAuxWindowStepTargets
open NumberedWindowInternalAuxWindowStepPrograms (exact_WindowPrimitiveLeaves)

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

private theorem onAux (s : Settings) (base : Program 2) (T : Program 1) (cal : TypeGuardCalibrated s T)
    (i old ctx dom cod fn arg : Nat) (read : unpackNode (i+1) = some (6,[dom,cod,fn,arg])) :
    evaluate (windowUpdate base T) (tape i old ctx) = rowValue s base i old ctx := by
  have fs := termFields read
  have d := fieldValue i old ctx 0 dom fs.1
  have c := fieldValue i old ctx 1 cod fs.2.1
  have fnCode := fieldValue i old ctx 2 fn fs.2.2.1
  have argCode := fieldValue i old ctx 3 arg fs.2.2.2
  have smallFn := (nodeBounds read).2 fn (by simp)
  have smallArg := (nodeBounds read).2 arg (by simp)
  have shapeEarlier : evaluate certain (tape i old ctx) = 1 := by
    simp only [certain,conjunctionOne]
    exact ⟨(shape i old ctx).mpr ⟨dom,cod,fn,arg,read⟩,
      earlier i old ctx 2 fn fnCode smallFn,earlier i old ctx 3 arg argCode smallArg⟩
  have bits : evaluate (admittedChildren T) (tape i old ctx) = 1 ↔
      typeGuard s dom = true ∧ typeGuard s cod = true ∧
      evaluate lookup ((i-fn) ::ᵥ old ::ᵥ nil) = arrow dom cod + 1 ∧
      evaluate lookup ((i-arg) ::ᵥ old ::ᵥ nil) = dom+1 := by
    simp only [admittedChildren,conjunctionOne,guardOne s T cal i old ctx 0 dom d,
      guardOne s T cal i old ctx 1 cod c,agrees,rowReport i old ctx 2 fn fnCode,
      rowReport i old ctx 3 arg argCode,rightType i old ctx dom cod d c,
      argumentCode,ownType 0 i old ctx dom d]
  rw [windowUpdate,evalBranch,actualConjunctionEvaluation,shapeEarlier,binaryValue,current,
    resultCode,ownType 1 i old ctx cod c,rowValue,read]
  let fallback := evaluate base (ctx ::ᵥ (i+1) ::ᵥ nil)
  let h := typeGuard s dom = true ∧ typeGuard s cod = true ∧
      evaluate lookup ((i-fn) ::ᵥ old ::ᵥ nil) = arrow dom cod + 1 ∧
      evaluate lookup ((i-arg) ::ᵥ old ::ᵥ nil) = dom+1
  change (if (if (1=1 ∧ evaluate (admittedChildren T) (tape i old ctx)=1) then 1 else 0) = 0
    then fallback else cod+1) = (if fn < i+1 ∧ arg < i+1 ∧ h then cod+1 else fallback)
  by_cases accepted : h
  · have yes := bits.mpr accepted
    simp [smallFn,smallArg,yes,accepted]
  · have no := fun yes => accepted (bits.mp yes)
    simp [smallFn,smallArg,no,accepted]

theorem exact_PhysicalAuxWindowStep : ExactPhysicalAuxWindowStep := by
  intro s base T cal i old ctx
  change evaluate (windowUpdate base T) (tape i old ctx) = _
  by_cases hit : ∃ dom cod fn arg, unpackNode (i+1) = some (6,[dom,cod,fn,arg])
  · obtain ⟨dom,cod,fn,arg,read⟩ := hit
    exact onAux s base T cal i old ctx dom cod fn arg read
  · have someOther : evaluate shapeCheck (tape i old ctx) ≠ 1 := fun checked => hit ((shape i old ctx).mp checked)
    have rejected : evaluate (InternalAcceptance.conjunction certain (admittedChildren T)) (tape i old ctx) = 0 := by
      rw [actualConjunctionEvaluation,certain,actualConjunctionEvaluation]
      simp [someOther]
    rw [windowUpdate,evalBranch,rejected,if_pos rfl,binaryValue,current]
    unfold rowValue
    split
    next dom cod fn arg read => exact False.elim (hit ⟨dom,cod,fn,arg,read⟩)
    next => rfl

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

theorem exact_PhysicalAuxWindow : ExactPhysicalAuxWindow := by
  intro s base T hBase hT ctx ty raw
  have memo := exact_IntrinsicMemoCalibration s base (windowUpdate base T) hBase (exact_PhysicalAuxWindowStep s base T hT)
  rw [queryEval,memo,exact_PackedIntrinsicProjection]
  by_cases yes : intrinsicWindow s ctx raw = ty+1 <;> simp [yes]

#print axioms exact_WindowPrimitiveLeaves
#print axioms exact_PhysicalAuxWindowStep
#print axioms exact_PhysicalAuxWindow

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepChecks
