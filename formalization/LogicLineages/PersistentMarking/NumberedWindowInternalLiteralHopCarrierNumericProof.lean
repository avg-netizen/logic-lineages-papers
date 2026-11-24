module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHopCarrierDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
import LogicLineages.PersistentMarking.NumberedWindowRawClassSaturationChecks
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeNumericFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHopCarrierNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open InternalEqualityTestEvaluationProof (vectorOne vectorThree)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings scalar canonical admitted least)
open NumberedWindowAddressAlgorithm (contextView typeBit addressView)
open NumberedWindowFieldAlgorithm (unpack packNode)
open NumberedWindowConcreteCheckers (step)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets (ActualContextGuard ActualTypeGuard)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowInternalSparsePathAdvanceTargets
  (ActualRawCalibration ActualLeastCalibration packedRaw packedLeast encodeState)
open NumberedWindowRawClassSaturationChecks (exact_RawLeastClosureWithVertices)
open NumberedWindowRawExchangeVerticesChecks (exact_OriginalGuardedEdgeVertices)
open NumberedWindowInternalAtomicApplicationShapeNumericFieldsProof (exactEmitters)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (predEvaluation)
open NumberedWindowInternalLiteralAuxRootNumericProof (packedReads)
open NumberedWindowInternalLiteralHopCarrier

private abbrev tape (ctx ty q w r : Nat) := ctx ::ᵥ ty ::ᵥ q ::ᵥ w ::ᵥ r ::ᵥ nil

private theorem slotValue (p : Program 1) (v : List.Vector Nat 5) (i : Fin 5) :
    evaluate (atSlot p i) v = evaluate p (v.get i ::ᵥ nil) := by
  unfold atSlot
  rw [evaluate,vectorOne]
  rfl

private theorem leastValue (L : Program 3) (ctx ty q w r : Nat) :
    evaluate (targetLeast L) (tape ctx ty q w r) = evaluate L (ctx ::ᵥ ty ::ᵥ r ::ᵥ nil) := by
  unfold targetLeast
  rw [evaluate,vectorThree]
  rfl

private theorem scalarValue (s : Settings) (i : Program 1) (L : Program 3)
    (scalarFit : ActualScalarCalibration s i) (ctx ty q w r k : Nat)
    (reported : evaluate (targetLeast L) (tape ctx ty q w r) = k+1) :
    evaluate (targetScalar i L) (tape ctx ty q w r) = (scalar s (packNode 3 [ctx,ty,k])).toNat := by
  unfold targetScalar
  rw [evaluate,vectorOne]
  change evaluate i (evaluate (targetAddress L) (tape ctx ty q w r) ::ᵥ nil) = _
  rw [scalarFit]
  have address : evaluate (targetAddress L) (tape ctx ty q w r) = packNode 3 [ctx,ty,k] := by
    unfold targetAddress
    rw [evaluate,vectorThree]
    change evaluate NumberedWindowInternalAtomicApplicationShape.addressEmitter
      (ctx ::ᵥ ty ::ᵥ evaluate (targetCode L) (tape ctx ty q w r) ::ᵥ nil) = _
    have v : evaluate (targetCode L) (tape ctx ty q w r) = k := by
      unfold targetCode
      rw [evaluate,vectorOne]
      change evaluate NumberedWindowInternalFreshProbeDispatchProgram.predOne
        (evaluate (targetLeast L) (tape ctx ty q w r) ::ᵥ nil) = _
      rw [predEvaluation,reported]
      rfl
    rw [v]
    exact exactEmitters.1 ctx ty k
  rw [address]

private theorem parsedFromView {ctx : Nat} {g : List Nat}
    (view : contextView ctx = some g) : unpack ctx = some g := by
  cases parsed : unpack ctx with
  | none => simp [contextView,parsed] at view
  | some row =>
    simp [contextView,parsed] at view
    exact congrArg some view.2

private theorem scalarOfOriginalTarget (entries : Entries) (s : Settings)
    (ctx ty q w r k : Nat) (g : List Nat)
    (view : contextView ctx = some g) (type : typeBit ty = true)
    (raw : packedRaw entries s ctx ty q w r = true)
    (normal : packedLeast s ctx ty r = some k) :
    scalar s (packNode 3 [ctx,ty,k]) = true := by
  have pctx := parsedFromView view
  have run : step entries s g ty q w r = true := by simpa [packedRaw,pctx] using raw
  have h : least s g ty r = some k := by simpa [packedLeast,pctx] using normal
  have admittedR : admitted s g ty r = true := (Bool.and_eq_true_iff.mp run).2
  have got := exact_RawLeastClosureWithVertices s g ty (exact_OriginalGuardedEdgeVertices s g ty)
    r k admittedR h
  simp [scalar,addressView,packedReads,view,type,canonical,got.2.1,got.2.2]

/-- The physical guard preserves the complete original raw callback,
including invalid contexts and a raw success without a least. -/
theorem exact_RawWithTargetCalibration (entries : Entries) (s : Settings) (i cv tv : Program 1)
    (raw : Program 5) (L : Program 3)
    (scalarFit : ActualScalarCalibration s i) (contextFit : ActualContextGuard cv)
    (typeFit : ActualTypeGuard tv) (rawFit : ActualRawCalibration entries s raw)
    (leastFit : ActualLeastCalibration s L) :
    ActualRawCalibration entries s (rawWithTarget i cv tv raw L) := by
  intro ctx ty q w r
  change evaluate (rawWithTarget i cv tv raw L) (tape ctx ty q w r) = _
  rw [rawWithTarget,actualConjunctionEvaluation,rawFit]
  cases rawAccepted : packedRaw entries s ctx ty q w r with
  | false => rfl
  | true =>
    have gate : evaluate (targetGate i cv tv L) (tape ctx ty q w r) = 1 := by
      rw [targetGate,evalBranch,addressGuards,actualConjunctionEvaluation,slotValue,slotValue]
      have cfit : evaluate cv ((tape ctx ty q w r).get 0 ::ᵥ nil) = (contextView ctx).isSome.toNat :=
        contextFit ctx
      have tfit : evaluate tv ((tape ctx ty q w r).get 1 ::ᵥ nil) = (typeBit ty).toNat :=
        typeFit ty
      simp only [cfit,tfit]
      cases view : contextView ctx with
      | none => rfl
      | some g =>
        cases dt : typeBit ty with
        | false => rfl
        | true =>
          have good : (Option.isSome (some g)).toNat = 1 ∧ true.toNat = 1 := ⟨rfl,rfl⟩
          rw [if_pos good,if_neg (by decide : (1 : Nat) ≠ 0),evalBranch]
          have lv : evaluate (targetLeast L) (tape ctx ty q w r) =
              encodeState (packedLeast s ctx ty r) := by rw [leastValue,leastFit]
          cases lk : packedLeast s ctx ty r with
          | none => rw [lv,lk]; rfl
          | some k =>
            have ready : evaluate (targetLeast L) (tape ctx ty q w r) = k+1 := lv.trans (congrArg encodeState lk)
            rw [ready,if_neg (Nat.succ_ne_zero k),scalarValue s i L scalarFit ctx ty q w r k ready,
              scalarOfOriginalTarget entries s ctx ty q w r k g view dt rawAccepted lk]
            rfl
    simp [gate]

#print axioms exact_RawWithTargetCalibration
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHopCarrierNumericProof
