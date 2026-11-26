import LogicLineages.PersistentMarking.ProtectedSpineSoundOwnerProof
import LogicLineages.PersistentMarking.ProtectedSpineSoundListProof
import LogicLineages.PersistentMarking.MarkedConstructorHeadExactProof
import LogicLineages.PersistentMarking.PortHeadObservationProof

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundHeadProof
open Spine DecisionPorts DecisionObservations FiniteDomainSchema HereditaryDomainCode
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineSoundStageTargets
open MarkedConstructorTargets (WholeWitness)
open MarkedConstructorTests (terms)

theorem children (F : Inputs S) (Γ : Context) (g : Head) (ts : Args)
    (hw : WellFormed F.data.types F.data.ports Γ) (ht : Observed F Γ (.head g ts)) :
    ∀ t, t ∈ terms ts → Observed F Γ t := by
  intro t hm
  obtain ⟨i,hi⟩ := ProtectedSpineSoundListProof.atMember hm
  exact PortHeadObservationProof.headObservations S F Γ g ts hw ht i t hi

theorem whole (F : Inputs S) (M : Code) (f : Head) (τ : Ty) (Γ : Context)
    (cs : List Code) (xs : List MarkedExtras.Tagged) (bs es ts : Args)
    (ho : OwnerRelated F (f,τ,Γ,cs,xs) bs es) (hM : FamilyRelated F M)
    (hts : ∀ t, t ∈ terms ts → Observed F Γ t)
    (h : WholeWitness (domain F) F.data.sourceHeads M (f,τ,Γ,cs,xs) (terms ts)) :
    Whole S f bs es ts := by
  cases ts with
  | nil => exact .nil
  | cons t ts =>
    have hObs := hts t List.mem_cons_self
    have hw := ho.1.2.2.1
    have ht := DecisionSourceBasicProof.rootType _ _ _ _ _
      (PortStateProof.observedUniverse S F Γ t hw hObs)
    obtain ⟨c,hc,hbit⟩ := h t List.mem_cons_self
    have hr := hM (f,t.type,Γ,cs,xs) c bs es
      (ProtectedSpineSoundOwnerProof.retype F f τ t.type Γ cs xs bs es ho ht) hc
    exact .cons ((ProtectedSpineSoundBitProof.bits F Γ t.type (.marked f t.type bs es) t c hw hObs hr).1 hbit)
      (whole F M f τ Γ cs xs bs es ts ho hM
        (fun u hu => hts u (List.mem_cons_of_mem _ hu)) (fun u hu => h u (List.mem_cons_of_mem _ hu)))
termination_by sizeOf ts

theorem copy (F : Inputs S) (M : Code) (f : Head) (τ : Ty) (Γ : Context)
    (cs : List Code) (xs : List MarkedExtras.Tagged) (bs es : Args) (t : Expr)
    (ho : OwnerRelated F (f,τ,Γ,cs,xs) bs es) (hM : FamilyRelated F M)
    (hObs : t ∈ observations F.data.names F.data.ports Γ F.target τ)
    (h : MarkedConstructorTests.copyTest S (domain F) F.data.sourceHeads M (f,τ,Γ,cs,xs) t = true) :
    Weak S (.marked f τ bs es) t := by
  obtain ⟨g,ts,rfl,hTy,hPre,hWhole⟩ :=
    (MarkedConstructorHeadExactProof.copy S (domain F) F.data.sourceHeads M (f,τ,Γ,cs,xs) t).mp h
  change g.result = τ at hTy
  subst τ
  exact .copy ho.2.1 (ProtectedSpineSoundBitProof.observedPaper F Γ g.result (.head g ts) hObs) hPre
    (whole F M f g.result Γ cs xs bs es ts ho hM (children F Γ g ts ho.1.2.2.1 hObs) hWhole)

theorem stat (F : Inputs S) (M : Code) (f : Head) (τ : Ty) (Γ : Context)
    (cs : List Code) (xs : List MarkedExtras.Tagged) (bs es : Args) (t : Expr)
    (ho : OwnerRelated F (f,τ,Γ,cs,xs) bs es) (hM : FamilyRelated F M)
    (hObs : t ∈ observations F.data.names F.data.ports Γ F.target τ)
    (h : MarkedConstructorTests.statTest S (domain F) F.data.sourceHeads M (f,τ,Γ,cs,xs) t = true) :
    Weak S (.marked f τ bs es) t := by
  obtain ⟨g,ts,rfl,hTy,hEq,hMulti,hWhole⟩ :=
    (MarkedConstructorHeadExactProof.stat S (domain F) F.data.sourceHeads M (f,τ,Γ,cs,xs) t).mp h
  change g.result = τ at hTy
  subst τ
  have hObsChildren := children F Γ g ts ho.1.2.2.1 hObs
  exact .stat ho.2.1 (ProtectedSpineSoundBitProof.observedPaper F Γ g.result (.head g ts) hObs) hEq
    (ProtectedSpineSoundListProof.multiset F Γ ho.1.2.2.1 ho.2.2.2.1 hObsChildren hMulti)
    (whole F M f g.result Γ cs xs bs es ts ho hM hObsChildren hWhole)

end LogicLineages.PersistentMarking.ProtectedSpineSoundHeadProof
