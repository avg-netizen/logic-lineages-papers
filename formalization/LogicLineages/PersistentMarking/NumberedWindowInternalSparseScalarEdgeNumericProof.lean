module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open ID1Completion
open InternalAcceptance (conjunction)
open InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open InternalEqualityTestEvaluationProof (vectorTwo vectorThree)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowScalarAlgorithm (edge)
open NumberedWindowInternalSparseDirectedSeen (edgeTape)
open NumberedWindowInternalSparseTypedRawTargets (packedWindow)
open NumberedWindowInternalSparseScalarEdge
open NumberedWindowInternalSparseScalarEdgeTargets

private theorem ofFour (f : Fin 4 → Nat) :
    List.Vector.ofFn f = f 0 ::ᵥ f 1 ::ᵥ f 2 ::ᵥ f 3 ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_
    (fun l => Fin.cases ?_ (fun x => Fin.elim0 x) l) k) j) i <;> simp <;> rfl

private theorem selectTwo (p : Program 2) (i j : Fin 4) (xs : List.Vector Nat 4) :
    evaluate (.composition p ![.projection i,.projection j]) xs =
      evaluate p (xs.get i ::ᵥ xs.get j ::ᵥ nil) := by
  change evaluate p (List.Vector.ofFn (fun b : Fin 2 =>
    evaluate ((![.projection i,.projection j] : Fin 2 → Program 4) b) xs)) = _
  rw [vectorTwo] <;> rfl

private theorem selectThree (p : Program 3) (i j k : Fin 4) (xs : List.Vector Nat 4) :
    evaluate (.composition p ![.projection i,.projection j,.projection k]) xs =
      evaluate p (xs.get i ::ᵥ xs.get j ::ᵥ xs.get k ::ᵥ nil) := by
  change evaluate p (List.Vector.ofFn (fun b : Fin 3 =>
    evaluate ((![.projection i,.projection j,.projection k] : Fin 3 → Program 4) b) xs)) = _
  rw [vectorThree] <;> rfl

private theorem bitGate (p q : Program 4) (xs : List.Vector Nat 4) (a b : Bool)
    (left : evaluate p xs = a.toNat) (right : evaluate q xs = b.toNat) :
    evaluate (conjunction p q) xs = (a && b).toNat := by
  have h := actualConjunctionEvaluation 4 p q xs
  rw [h,left,right]
  cases a <;> cases b <;> rfl

/-- Both original endpoint checks are evaluated at the same actual
decoded context, including failed unpack and successful empty context. -/
theorem calibration : ExactPackedScalarEdgeCalibration := by
  intro s X W xCal wCal ctx ty w v
  let xs : List.Vector Nat 4 := ctx ::ᵥ ty ::ᵥ w ::ᵥ v ::ᵥ nil
  let raw := (NumberedWindowExchangeAlgorithm.bits s.equivalentHeads w v).1
  let a := packedWindow s ctx ty w
  let b := packedWindow s ctx ty v
  have rawOut : evaluate (exchangeCall X) xs = raw.toNat := by
    rw [exchangeCall,selectTwo]
    have h := xCal w v
    rw [vectorTwo] at h
    exact h
  have aOut : evaluate (sourceWindow W) xs = a.toNat := by
    rw [sourceWindow,selectThree]
    exact wCal ctx ty w
  have bOut : evaluate (targetWindow W) xs = b.toNat := by
    rw [targetWindow,selectThree]
    exact wCal ctx ty v
  have combined : evaluate (edge4 X W) xs = (raw && (a && b)).toNat :=
    bitGate _ _ xs _ _ rawOut (bitGate _ _ xs _ _ aOut bOut)
  rw [ofFour]
  change evaluate (edge4 X W) xs = (packedEdge s ctx ty w v).toNat
  rw [combined]
  cases decoded : unpack ctx <;>
    simp [raw,a,b,packedEdge,packedWindow,decoded,edge,Bool.and_assoc]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeNumericProof
