module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector InternalListCodec
open InternalEqualityTestEvaluationProof InternalPairingEvaluationProof InternalUnpairEvaluationProof

/-- The successor AST is calibrated to the actual source's left-hand 1 + code. -/
theorem consEvaluation (h t : Nat) :
    evaluate consCode (h ::ᵥ t ::ᵥ List.Vector.nil) = 1 + Nat.pair h t := by
  change Nat.succ (evaluate InternalPairing.pairing (h ::ᵥ t ::ᵥ List.Vector.nil)) = _
  rw [exactPairingEvaluation,Nat.add_comm 1]

theorem headEvaluation (n : Nat) :
    evaluate headCode (n ::ᵥ List.Vector.nil) = (Nat.unpair (n-1)).1 := by
  change evaluate InternalUnpair.left (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate InternalEqualityTest.predecessor (n ::ᵥ List.Vector.nil)) = _
  rw [vectorOne,exactPredecessorEvaluation,Nat.pred_eq_sub_one]
  exact (exactUnpairEvaluation (n-1)).1

theorem tailEvaluation (n : Nat) :
    evaluate tailCode (n ::ᵥ List.Vector.nil) = (Nat.unpair (n-1)).2 := by
  change evaluate InternalUnpair.right (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate InternalEqualityTest.predecessor (n ::ᵥ List.Vector.nil)) = _
  rw [vectorOne,exactPredecessorEvaluation,Nat.pred_eq_sub_one]
  exact (exactUnpairEvaluation (n-1)).2

theorem nilEvaluation (n : Nat) :
    evaluate nilTest (n ::ᵥ List.Vector.nil) = if n=0 then 1 else 0 :=
  zeroTestEvaluation n

theorem exactListCodecEvaluation : InternalListCodecEvaluationTargets.ExactListCodecEvaluation :=
  ⟨consEvaluation, fun n => ⟨headEvaluation n,tailEvaluation n,nilEvaluation n⟩⟩

/-- This external theorem names the original source encoder, not a replacement. -/
theorem exactSourceListEncoding : InternalListCodecEvaluationTargets.ExactSourceListEncoding := by
  constructor
  · constructor
    · rfl
    · exact nilEvaluation 0
  · intro h t
    simp only [consEvaluation,headEvaluation,tailEvaluation,nilEvaluation,
      NumberedMultisetNumeric.numbersNumber]
    simp [Nat.add_comm 1,Nat.unpair_pair]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
