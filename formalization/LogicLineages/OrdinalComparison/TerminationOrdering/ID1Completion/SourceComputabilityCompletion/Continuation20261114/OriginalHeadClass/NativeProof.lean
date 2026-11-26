module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.NativeProof
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHeadEncodingBridge.NativeProof (chooseEvaluation projectionOne)

theorem payloadEvaluation (tag raw : Nat) :
    evaluate (atPayload tag) (raw ::ᵥ List.Vector.nil) =
    evaluate (branchClass tag) ((Nat.unpair raw).2 ::ᵥ List.Vector.nil) := by
  rw [atPayload,unaryCompositionEvaluation,rightEvaluation]
  rfl

theorem nativeClass (n : Nat) (h : HeadCode (Fin n)) :
    evaluate headClass (List.Vector.ofFn ![headNumber h]) =
      NumberedExchangeGuardsPrimrecProof.headClassNumber h := by
  change evaluate headClass (headNumber h ::ᵥ List.Vector.nil) = _
  cases h <;> simp [headClass,chooseEvaluation,headNumber,Nat.unpair_pair,payloadEvaluation,
    branchClass,constantEvaluation,succOfEvaluation,projectionOne,
    NumberedExchangeGuardsPrimrecProof.headClassNumber,Nat.add_comm] <;> omega

theorem equivalentValue (x y : Nat) :
    evaluate equivalent (List.Vector.ofFn ![x,y]) =
      if evaluate headClass (List.Vector.ofFn ![x]) = evaluate headClass (List.Vector.ofFn ![y])
      then 1 else 0 := by
  change evaluate (sameOf leftClass rightClass) (List.Vector.ofFn ![x,y]) = _
  rw [sameOfEvaluation]
  rfl

theorem nativeEquivalence (n : Nat) (f g : HeadCode (Fin n)) :
    evaluate equivalent (List.Vector.ofFn ![headNumber f,headNumber g]) =
      (decide (RecursiveComparison.headEquivalent (NumberedAuxiliaryDecoding.decodeHead f)
        (NumberedAuxiliaryDecoding.decodeHead g))).toNat := by
  rw [equivalentValue,nativeClass,nativeClass]
  have h := NumberedExchangeGuardsPrimrecProof.headClassNumberCalibration f g
  by_cases hc : NumberedExchangeGuardsPrimrecProof.headClassNumber f =
      NumberedExchangeGuardsPrimrecProof.headClassNumber g
  · simp [hc,h.mp hc]
  · have hn : ¬ RecursiveComparison.headEquivalent (NumberedAuxiliaryDecoding.decodeHead f)
        (NumberedAuxiliaryDecoding.decodeHead g) := fun he => hc (h.mpr he)
    rw [if_neg hc,decide_eq_false hn]
    rfl

theorem nativeClassAndEquivalence : Targets.NativeClassAndEquivalence :=
  ⟨nativeClass,nativeEquivalence⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.NativeProof
