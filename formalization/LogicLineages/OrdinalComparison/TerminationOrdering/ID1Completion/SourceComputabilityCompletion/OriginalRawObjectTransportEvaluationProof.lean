module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportEvaluationProof
open OriginalRawObjectTransport OriginalRawSyntaxTransport
open InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalEqualityTestEvaluationProof (vectorOne)
open InternalListCodecEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Calibration is on arbitrary naturals, with no decoding or typed premise. -/
theorem shiftPackedEvaluation (k packed : Nat) :
    evaluate shiftPackedRaw (List.Vector.ofFn ![k,packed]) =
      Nat.pair (Nat.unpair packed).1
        (evaluate shiftRaw (List.Vector.ofFn ![k,(Nat.unpair packed).2])) := by
  unfold shiftPackedRaw
  rw [pairOfEvaluation,leftOfEvaluation]
  change Nat.pair (Nat.unpair packed).1
    (evaluate shiftRaw (List.Vector.ofFn ![k,
      evaluate (rightOf (.projection 1)) (List.Vector.ofFn ![k,packed])])) = _
  rw [rightOfEvaluation]
  rfl

theorem erasePackedEvaluation (d k packed : Nat) :
    evaluate erasePackedRaw (List.Vector.ofFn ![d,k,packed]) =
      Nat.pair (Nat.unpair packed).1
        (evaluate eraseRaw (List.Vector.ofFn ![d,k,(Nat.unpair packed).2])) := by
  unfold erasePackedRaw
  rw [pairOfEvaluation,leftOfEvaluation]
  change Nat.pair (Nat.unpair packed).1
    (evaluate eraseRaw (List.Vector.ofFn ![d,k,
      evaluate (rightOf (.projection 2)) (List.Vector.ofFn ![d,k,packed])])) = _
  rw [rightOfEvaluation]
  rfl

theorem rankPackedEvaluation (packed : Nat) :
    evaluate variableRankPackedRaw (List.Vector.ofFn ![packed]) =
      evaluate variableRankRaw (List.Vector.ofFn ![(Nat.unpair packed).2]) := by
  change evaluate variableRankRaw (List.Vector.ofFn ![
    evaluate InternalUnpair.right (List.Vector.ofFn ![packed])]) = _
  rw [rightEvaluation]
  rfl

theorem shiftObjectEvaluation (d input : Nat) :
    evaluate shiftObjectRaw (List.Vector.ofFn ![d,input]) =
      Nat.pair (1 + Nat.pair d (Nat.unpair input).1)
        (evaluate shiftPackedRaw (List.Vector.ofFn ![0,(Nat.unpair input).2])) := by
  unfold shiftObjectRaw
  rw [pairOfEvaluation,consOfEvaluation,leftOfEvaluation]
  change Nat.pair (1 + Nat.pair d (Nat.unpair input).1)
    (evaluate shiftPackedRaw (List.Vector.ofFn ![0,
      evaluate (rightOf (.projection 1)) (List.Vector.ofFn ![d,input])])) = _
  rw [rightOfEvaluation]
  rfl

theorem eraseContextEvaluation (input : Nat) :
    evaluate (.composition InternalListCodec.tailCode (fun _ : Fin 1 => InternalUnpair.left))
      (List.Vector.ofFn ![input]) = (Nat.unpair ((Nat.unpair input).1 - 1)).2 := by
  change evaluate InternalListCodec.tailCode (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate InternalUnpair.left (List.Vector.ofFn ![input])) = _
  rw [leftEvaluation,vectorOne,tailEvaluation]
  rfl

theorem eraseDomainEvaluation (input : Nat) :
    evaluate (.composition InternalListCodec.headCode (fun _ : Fin 1 => InternalUnpair.left))
      (List.Vector.ofFn ![input]) = (Nat.unpair ((Nat.unpair input).1 - 1)).1 := by
  change evaluate InternalListCodec.headCode (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate InternalUnpair.left (List.Vector.ofFn ![input])) = _
  rw [leftEvaluation,vectorOne,headEvaluation]
  rfl

theorem eraseObjectEvaluation (input : Nat) :
    evaluate eraseObjectRaw (List.Vector.ofFn ![input]) =
      Nat.pair (Nat.unpair ((Nat.unpair input).1 - 1)).2
        (evaluate erasePackedRaw (List.Vector.ofFn ![
          (Nat.unpair ((Nat.unpair input).1 - 1)).1,0,(Nat.unpair input).2])) := by
  unfold eraseObjectRaw
  rw [pairOfEvaluation,eraseContextEvaluation]
  change Nat.pair (Nat.unpair ((Nat.unpair input).1 - 1)).2
    (evaluate erasePackedRaw (List.Vector.ofFn ![
      evaluate (.composition InternalListCodec.headCode (fun _ : Fin 1 => InternalUnpair.left))
        (List.Vector.ofFn ![input]),0,
      evaluate InternalUnpair.right (List.Vector.ofFn ![input])])) = _
  rw [eraseDomainEvaluation,rightEvaluation]
  rfl

theorem rankObjectEvaluation (input : Nat) :
    evaluate variableRankObjectRaw (List.Vector.ofFn ![input]) =
      evaluate variableRankPackedRaw (List.Vector.ofFn ![(Nat.unpair input).2]) := by
  change evaluate variableRankPackedRaw (List.Vector.ofFn ![
    evaluate InternalUnpair.right (List.Vector.ofFn ![input])]) = _
  rw [rightEvaluation]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportEvaluationProof
