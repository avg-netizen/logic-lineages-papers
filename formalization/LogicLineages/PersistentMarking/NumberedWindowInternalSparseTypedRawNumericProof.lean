module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction)
open InternalEqualityTestEvaluationProof (vectorOne vectorThree)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowRawContextAlgorithm (run)
open NumberedWindowInternalSparseRawRun (ownRun)
open NumberedWindowInternalSparseRawRunChecks (exact_OriginalOwnRawRun)
open NumberedWindowInternalSparsePathAdvanceTargets (packedRaw)
open NumberedWindowInternalSparseTypedRaw
open NumberedWindowInternalSparseTypedRawTargets

private theorem selectOne (p : Program 1) (i : Fin 5) (v : List.Vector Nat 5) :
    evaluate (.composition p (fun _ : Fin 1 => .projection i)) v =
      evaluate p (v.get i ::ᵥ nil) := by
  change evaluate p (List.Vector.ofFn (fun _ : Fin 1 => v.get i)) = _
  rw [vectorOne]

private theorem selectThree (p : Program 3) (i j k : Fin 5) (v : List.Vector Nat 5) :
    evaluate (.composition p ![.projection i,.projection j,.projection k]) v =
      evaluate p (v.get i ::ᵥ v.get j ::ᵥ v.get k ::ᵥ nil) := by
  change evaluate p (List.Vector.ofFn (fun b : Fin 3 =>
    evaluate ((![.projection i,.projection j,.projection k] : Fin 3 → Program 5) b) v)) = _
  rw [vectorThree] <;> rfl

private theorem bitGate (p q : Program 5) (v : List.Vector Nat 5) (a b : Bool)
    (left : evaluate p v = a.toNat) (right : evaluate q v = b.toNat) :
    evaluate (conjunction p q) v = (a && b).toNat := by
  rw [conjunctionEvaluation,left,right]
  cases a <;> cases b <;> rfl

private theorem bitIndicator (b : Bool) : b.toNat = (if b then 1 else 0) := by
  cases b <;> rfl

theorem calibration : ExactTypedRaw5Calibration := by
  intro entries s root other wp syn rootCal otherCal syntaxCal windowCal ctx ty q w r
  let v : List.Vector Nat 5 := ctx ::ᵥ ty ::ᵥ q ::ᵥ w ::ᵥ r ::ᵥ nil
  let sq := (NumberedWindowSyntaxAlgorithm.syntaxBits q).1
  let sr := (NumberedWindowSyntaxAlgorithm.syntaxBits r).1
  let stepped := run (NumberedWindowConcreteCheckers.root entries s) w q w r
  let aq := packedWindow s ctx ty q
  let ar := packedWindow s ctx ty r
  have sqOut : evaluate (sourceSyntax syn) v = sq.toNat := by
    rw [sourceSyntax,selectOne]
    exact syntaxCal q
  have srOut : evaluate (destinationSyntax syn) v = sr.toNat := by
    rw [destinationSyntax,selectOne]
    exact syntaxCal r
  have ownOut : evaluate (ownCheck root other) v = stepped.toNat := by
    rw [ownCheck,selectThree]
    exact exact_OriginalOwnRawRun _ root other rootCal otherCal q w r
  have aqOut : evaluate (sourceWindow wp) v = aq.toNat := by
    rw [sourceWindow,selectThree]
    exact windowCal ctx ty q
  have arOut : evaluate (destinationWindow wp) v = ar.toNat := by
    rw [destinationWindow,selectThree]
    exact windowCal ctx ty r
  have selected : evaluate (typedRaw5 root other wp syn) v =
      (((sq && sr) && stepped) && (aq && ar)).toNat :=
    bitGate _ _ v _ _ (bitGate _ _ v _ _ (bitGate _ _ v _ _ sqOut srOut) ownOut)
      (bitGate _ _ v _ _ aqOut arOut)
  change evaluate (typedRaw5 root other wp syn) v = if packedRaw entries s ctx ty q w r then 1 else 0
  rw [selected,bitIndicator]
  cases decoded : unpack ctx <;>
    simp [sq,sr,stepped,aq,ar,packedWindow,packedRaw,decoded,NumberedWindowConcreteCheckers.step,
      NumberedWindowRawContextAlgorithm.windowStep,NumberedWindowRawContextAlgorithm.raw,Bool.and_assoc]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawNumericProof
