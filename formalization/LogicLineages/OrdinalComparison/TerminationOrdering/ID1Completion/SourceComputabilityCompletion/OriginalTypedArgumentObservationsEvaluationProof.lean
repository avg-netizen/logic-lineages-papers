module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEvaluationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRequestNumericBoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalTypedArgumentObservations InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof InternalAcceptanceCalibrationProof
open OriginalTypedDecoderEvaluationSupportProof OriginalRawSyntaxTransportEvaluationSupportProof
open NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedMultisetNumeric
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo)
attribute [local irreducible] InternalPairing.pairing InternalUnpair.left InternalUnpair.right InternalListCodec.consCode

/-- Existing pairing bounds make the literal raw tag7 tail strictly smaller;
no assertion that this raw constructor is a numeric-list cons. -/
theorem rawTailBound (typ child tail : Nat) :
 tail < Nat.pair 7 (Nat.pair typ (Nat.pair child tail)) := by
 have h1 := Nat.add_le_pair 7 (Nat.pair typ (Nat.pair child tail))
 have h2 := Nat.right_le_pair typ (Nat.pair child tail)
 have h3 := Nat.right_le_pair child tail
 omega

theorem numericTailBound (head tail : Nat) : tail < 1 + Nat.pair head tail := by
 have h := Nat.right_le_pair head tail
 omega

theorem childEvaluation (R : Program 2) (raw acc parameter : Nat) :
 evaluate (childObservation R) (Nat.pair raw acc ::ᵥ parameter ::ᵥ nil) =
 evaluate R (Nat.pair (Nat.unpair (Nat.unpair raw).2).1
   (Nat.unpair (Nat.unpair (Nat.unpair raw).2).2).1 ::ᵥ parameter ::ᵥ nil) := by
 change evaluate R (ofFn fun i : Fin 2 => evaluate
   ((![childPacked,.projection 1] : Fin 2 → Program 2) i) _) = _
 rw [vectorTwo]
 simp only [childPacked,childType,childRaw,payload,remaining,pairOfEvaluation,
   leftOfEvaluation,rightOfEvaluation,evaluate,Nat.unpair_pair]
 all_goals rfl

theorem stepNil (R : Program 2) (acc parameter : Nat) :
 evaluate (walkStep R) (Nat.pair (Nat.pair 6 0) acc ::ᵥ parameter ::ᵥ nil) =
 Nat.pair (Nat.pair 6 0) acc := by
 rw [walkStep,ifSameEvaluation]
 simp only [remaining,leftOfEvaluation,constantEvaluation,evaluate,Nat.unpair_pair]
 simp

theorem stepCons (R : Program 2) (typ child tail acc parameter : Nat) :
 evaluate (walkStep R)
   (Nat.pair (Nat.pair 7 (Nat.pair typ (Nat.pair child tail))) acc ::ᵥ parameter ::ᵥ nil) =
 Nat.pair tail (1 + Nat.pair (Nat.pair typ
   (evaluate R (Nat.pair typ child ::ᵥ parameter ::ᵥ nil))) acc) := by
 rw [walkStep,ifSameEvaluation]
 simp only [remaining,leftOfEvaluation,constantEvaluation,evaluate,Nat.unpair_pair,ite_true]
 simp only [advance,pairOfEvaluation,tailRaw,typedObservation,consOfEvaluation,
   accumulated,payload,rightOfEvaluation,leftOfEvaluation,remaining,childType,childEvaluation,evaluate,Nat.unpair_pair]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsEvaluationProof
