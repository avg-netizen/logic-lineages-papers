import LogicLineages.PersistentMarking.ProtectedSpineSoundBuilderProof
import LogicLineages.PersistentMarking.ProtectedSpineHeadValueProof

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundOrdinaryProof
open Spine DecisionPorts DecisionObservations FiniteDomainFoundation FiniteDomainSchema
open HereditaryDomainCode HereditaryDomainSemantics PortNormalization
open ProtectedSpineAdequacyTargets ProtectedSpineSoundRelation ProtectedSpineSoundStageTargets
open ProtectedSpineInterpreterCore (funTest ordinaryHead)

theorem ordinaryPaper (S : Signature) (f : Head) (bs : Args)
    (h : PaperTerm S (.marked f f.result bs .nil) f.result) : PaperTerm S (.head f bs) f.result := by
  cases h.1 with
  | marked hb he => exact ⟨.head hb,h.2.1,h.2.2.1⟩

theorem funHead (F : Inputs S) (M : Code) (f : Head) (Γ : Context)
    (base : List Code) (extras : List MarkedExtras.Tagged) (bs : Args)
    (ho : OwnerRelated F (f,f.result,Γ,base,extras) bs .nil) (t : Expr)
    (ht : t ∈ observations F.data.names F.data.ports Γ F.target f.result)
    (h : funTest S (domain F) (f,f.result,Γ,base,extras) t = true) :
    Weak S (.head f bs) t := by
  cases t <;> simp only [funTest,Bool.false_eq_true] at h
  rename_i g ts
  simp only [Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨hEq,hTy⟩,hMatch⟩ := h
  have hObs : Observed F Γ (.head g ts) := by
    unfold Observed
    change Expr.head g ts ∈ observations F.data.names F.data.ports Γ F.target g.result
    rw [←hTy]
    exact ht
  have hTarget := ProtectedSpineSoundBitProof.observedPaper F Γ g.result (.head g ts) (hTy ▸ ht)
  have hChildren := ProtectedSpineSoundHeadProof.children F Γ g ts ho.1.2.2.1 hObs
  have hMatch' := (MarkedConstructorOccurrenceProof.matching (domain F) Γ _ _).mp hMatch
  exact .funHead (ordinaryPaper S f bs ho.2.1) hTarget
    ((MarkedConstructorHeadExactProof.equivalent S f g).mp hEq) hTy
    (ProtectedSpineSoundListProof.matching F Γ ho.1.2.2.1 ho.2.2.2.1 ts hChildren hMatch')

theorem codeRelated (F : Inputs S) (M : Code) (f : Head) (Γ : Context)
    (base : List Code) (extras : List MarkedExtras.Tagged) (bs : Args)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (ho : OwnerRelated F (f,f.result,Γ,base,extras) bs .nil) (hM : FamilyRelated F M) :
    Related F f.result Γ
      (encode (domain F) f.result Γ (ordinaryHead S (domain F) F.data.sourceHeads M (f,f.result,Γ,base,extras)))
      (some (.head f bs)) := by
  let E := domain F
  let H := F.data.sourceHeads
  let p : MarkedFamilyParameters.Parameter := (f,f.result,Γ,base,extras)
  have hValid := ProtectedSpineHeadValueProof.valid false S E H M p (ProtectedSpineAdequacyBase.prefixClosed S F) hm ho.1
  have hEnc := HereditaryEncodeDecodeProof.encodeDecode E f.result Γ (ordinaryHead S E H M p) ho.1.2.2.1 hValid
  have hPaper := ordinaryPaper S f bs ho.2.1
  rw [Related.eq_def]
  refine ⟨hEnc.1,?_⟩
  intro Δ hd he
  obtain ⟨_,hBits,hApp⟩ := hEnc.2 Δ hd he
  constructor
  · intro t ht
    obtain ⟨hW,hS⟩ := hBits t ht
    have hTarget := ProtectedSpineSoundBitProof.observedPaper F Δ f.result t ht
    have hMark := ProtectedSpineSoundBuilderProof.weakAt F M p bs .nil Δ t hm ho hM hd he ht
    constructor
    · intro hb
      have hb' := hW.symm.trans hb
      change (funTest S E (MarkedFamilyCoherence.weakenParameter E p Δ) t ||
        (MarkedConstructorValue.build S E H M p).weak Δ t) = true at hb'
      simp only [Bool.or_eq_true] at hb'
      rcases hb' with hFun | hPut
      · let w := MarkedFamilyCoherence.weakenParameter E p Δ
        exact funHead F M f Δ w.2.2.2.1 w.2.2.2.2 bs
          (ProtectedSpineSoundOwnerProof.weaken F p Δ bs .nil ho hd he) t ht hFun
      · exact .put hPaper hTarget (hMark hPut)
    · intro hb
      exact .intro hPaper hTarget rfl (hMark (hS.symm.trans hb))
  · intro ds τ hp xs args hx ht hu hr
    rw [hApp ds τ hp xs hx,ProtectedSpineSoundTupleProof.ordinaryCall f τ bs args
      (ProtectedSpineSoundTupleProof.nonempty hp ht) ht]
    exact ProtectedSpineSoundBuilderProof.tupleAt F M p bs .nil Δ hm ho hM hd he ds τ hp xs args hx ht hu hr

end LogicLineages.PersistentMarking.ProtectedSpineSoundOrdinaryProof
