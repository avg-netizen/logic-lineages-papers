module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundVariableProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundHeadCases
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundLambdaProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundStageProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundInterpreterProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineSoundStageTargets
open ProtectedSpineSoundInterpreterTargets
open MarkedConstructorOperator (leastFixedPoint)

theorem exact_InterpreterSound : InterpreterSound := by
  intro S F M hm hM q
  exact @Expr.rec (ExprGoal F M) (ArgsGoal F M)
    (ProtectedSpineSoundVariableProof.free F M)
    (ProtectedSpineSoundVariableProof.bound F M)
    (fun α q ih => ProtectedSpineSoundLambdaProof.lambda F M α q hm ih)
    (fun f bs ih => ProtectedSpineSoundHeadCases.ordinary F M f bs hm hM ih)
    (fun f σ bs es hb he => ProtectedSpineSoundHeadCases.marked F M f σ bs es hm hM hb he)
    (ProtectedSpineSoundHeadFrameProof.nilArgs F M)
    (ProtectedSpineSoundHeadFrameProof.consArgs F M)
    q

theorem exact_SoundObservation : ProtectedSpineSoundRelation.SoundObservation := by
  intro S F Γ q t σ hw hu ho hq ht
  let M := leastFixedPoint S (domain F) F.data.sourceHeads
  have hm := (ProtectedSpineAdequacyBase.fixed S F).1
  have hRelated := ProtectedSpineSoundStageProof.fixed F
  have hqTag := SpineShiftProof.annotationExact _ _ _ hq.1
  have htTag := SpineShiftProof.annotationExact _ _ _ ht.1
  have hObs : t ∈ DecisionObservations.observations F.data.names F.data.ports Γ F.target q.type := by
    rw [hqTag,←htTag]
    exact ho
  have hTyped : Typed EmptyContext q q.type := hqTag.symm ▸ hq.1
  have hf : Frame F Γ [] .nil [] := ⟨.nil,True.intro,.nil⟩
  have h := (exact_InterpreterSound S F M hm hRelated q Γ [] .nil [] hTyped hu hw hf).1
  rw [SubstitutionProof.emptySubstitution] at h
  exact ProtectedSpineSoundBitProof.bits F Γ q.type q t _ hw hObs h

#print axioms exact_InterpreterSound
#print axioms exact_SoundObservation
end LogicLineages.PersistentMarking.ProtectedSpineSoundInterpreterProof
