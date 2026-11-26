module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundBuilderProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineApplicationGapOldProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundStageProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics PortNormalization
open ProtectedSpineAdequacyTargets ProtectedSpineSoundRelation ProtectedSpineSoundStageTargets
open MarkedConstructorOperator (step nextFamily iterate leastFixedPoint)

theorem exact_StagePreservation : StagePreservation := by
  intro S F M hm hM p c bs es hp hc
  let E := domain F
  let H := F.data.sourceHeads
  let N := step S E H M
  have hStep := MarkedConstructorEndomapProof.endomap S E H (ProtectedSpineAdequacyBase.prefixClosed S F) M hm
  have hEnc := MarkedConstructorEncodingProof.encodeAt S E H M p (ProtectedSpineAdequacyBase.prefixClosed S F) hm hp.1
  have hEq := hStep.2.2 p hp.1
  change ValueEq E p.2.1 p.2.2.1
    (decode E p.2.1 p.2.2.1 (MarkedFamilyCoding.decode E H N p))
    (MarkedConstructorValue.build S E H M p) at hEq
  rw [StructuralMarkedActionProof.decoded E H N p c hc] at hEq
  have hc' := (MarkedConstructorLookupProof.actionValid E H N p c hc).2
  have hCodes := HereditaryEncodingCongruenceProof.injective E p.2.1 p.2.2.1 c (nextFamily S E H M p)
    hc' hEnc.1 (HereditaryValueEqualityProof.trans hEq (HereditaryValueEqualityProof.symm hEnc.2))
  rw [hCodes]
  exact ProtectedSpineSoundBuilderProof.build F M p bs es hm hp hM

theorem exact_IterationSound : IterationSound := by
  intro S F n
  let E := domain F
  let H := F.data.sourceHeads
  have hStep := MarkedConstructorEndomapProof.endomap S E H (ProtectedSpineAdequacyBase.prefixClosed S F)
  induction n with
  | zero =>
    intro p c bs es hp hc
    have h0 := ProtectedSpineApplicationGapOldProof.bottomOutput E H p hp.1
    have he : c = StructuralActions.bottom E p.2.1 p.2.2.1 := Option.some.inj (hc.symm.trans h0)
    rw [he]
    exact ProtectedSpineSoundRelationProof.bottomAt F p.2.1 p.2.2.1 _ hp.1.2.2.1
  | succ n ih =>
    exact exact_StagePreservation S F (iterate S E H n)
      (MarkedConstructorIterationProof.retained S E H hStep n) ih

theorem fixed (F : Inputs S) : FamilyRelated F (leastFixedPoint S (domain F) F.data.sourceHeads) :=
  exact_IterationSound S F _

#print axioms exact_StagePreservation
#print axioms exact_IterationSound
end LogicLineages.PersistentMarking.ProtectedSpineSoundStageProof
