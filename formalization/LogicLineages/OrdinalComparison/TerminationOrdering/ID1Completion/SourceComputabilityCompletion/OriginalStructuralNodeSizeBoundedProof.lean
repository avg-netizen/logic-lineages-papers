module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeTransitionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeBoundedProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open OriginalRawSyntaxTransportBoundedProof (initialEvaluation outputEvaluation)
open OriginalRawSyntaxTransportWeightProof (fuelEvaluation)
open OriginalStructuralNodeSizeTransitionEvaluationProof
open InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem iterateSuccessor (count initial : Nat) :
    evaluate OriginalStructuralNodeSize.iterate (List.Vector.ofFn ![count+1,initial]) =
      evaluate OriginalStructuralNodeSize.transition (List.Vector.ofFn ![
        evaluate OriginalStructuralNodeSize.iterate (List.Vector.ofFn ![count,initial])]) := by
  change evaluate OriginalStructuralNodeSize.transition (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate OriginalStructuralNodeSize.iterate (List.Vector.ofFn ![count,initial])) = _
  congr 1

theorem iterateEvaluation (count initial : Nat) :
    evaluate OriginalStructuralNodeSize.iterate (List.Vector.ofFn ![count,initial]) =
      OriginalStructuralNodeSize.iterateValue count initial := by
  induction count with
  | zero => rfl
  | succ count ih => rw [iterateSuccessor,transitionCalibration,ih]; rfl

theorem runEvaluation (v : List.Vector Nat 3) :
    evaluate OriginalStructuralNodeSize.run v =
      OriginalStructuralNodeSize.iterateValue (fuelValue (v.get 2))
        (initialValue (v.get 0) (v.get 1) (v.get 2)) := by
  rw [OriginalStructuralNodeSize.run,binaryCompositionEvaluation,fuelEvaluation,initialEvaluation,iterateEvaluation]

theorem rawEvaluation (input : Nat) :
    evaluate OriginalStructuralNodeSize.raw (List.Vector.ofFn ![input]) =
      OriginalStructuralNodeSize.rawValue input := by
  rw [OriginalStructuralNodeSize.raw,unaryCompositionEvaluation,outputEvaluation]
  change outputValue (evaluate (.composition OriginalStructuralNodeSize.run
    ![constant 1 0,constant 1 0,.projection 0]) (List.Vector.ofFn ![input])) = _
  rw [ternaryCompositionEvaluation,runEvaluation]
  rfl

theorem packedEvaluation (input : Nat) :
    evaluate OriginalStructuralNodeSize.packed (List.Vector.ofFn ![input]) =
      OriginalStructuralNodeSize.rawValue (Nat.unpair input).2 := by
  rw [OriginalStructuralNodeSize.packed,unaryCompositionEvaluation]
  change evaluate OriginalStructuralNodeSize.raw (List.Vector.ofFn ![(Nat.unpair input).2]) = _
  exact rawEvaluation _
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeBoundedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeBoundedProof
