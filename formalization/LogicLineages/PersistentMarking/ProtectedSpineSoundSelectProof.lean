import LogicLineages.PersistentMarking.ProtectedSpineSoundSourceProof
import LogicLineages.PersistentMarking.ProtectedSpineSoundHeadProof
import LogicLineages.PersistentMarking.MarkedConstructorSourceTupleProof
import LogicLineages.PersistentMarking.ProtectedSpineAdequacyBase
import LogicLineages.PersistentMarking.DecisionClosureCallProof

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundSelectProof
open Spine DecisionPorts DecisionObservations FiniteDomainFoundation FiniteDomainSchema
open HereditaryDomainCode HereditaryDomainSemantics PortNormalization
open ProtectedSpineAdequacyTargets ProtectedSpineSoundRelation ProtectedSpineSoundStageTargets
open MarkedFamilyParameters (Parameter)
open MarkedConstructorTargets (SelectWitness)

theorem ownerTupleRelated (F : Inputs S) (M : Code) (f : Head) (τ : Ty) (Γ : Context)
    (cs : List Code) (xs : List MarkedExtras.Tagged) (bs es : Args) (ds : List Ty) (vs : List Code)
    (ho : OwnerRelated F (f,τ,Γ,cs,xs) bs es) (hM : FamilyRelated F M)
    (ht : ∀ ρ, ρ ∈ ds → ρ ∈ F.data.types)
    (hv : MarkedConstructorTests.ownerTuple (domain F) F.data.sourceHeads M (f,τ,Γ,cs,xs) ds = some vs) :
    ∀ i ρ v a, ds[i]? = some ρ → vs[i]? = some v → At (ownerCopies f bs es ds) i a →
      Related F ρ Γ v (some a) := by
  induction ds generalizing vs with
  | nil => intro i ρ v a hd; simp at hd
  | cons d ds ih =>
    let get := MarkedConstructorTests.owner (domain F) F.data.sourceHeads M (f,τ,Γ,cs,xs)
    change (d::ds).mapM get = some vs at hv
    cases he : get d with
    | none => simp [List.mapM_cons,he] at hv
    | some cd =>
      cases hTail : ds.mapM get with
      | none => simp [List.mapM_cons,he,hTail] at hv
      | some tail =>
        have hv' : cd::tail = vs := by simpa [List.mapM_cons,he,hTail] using hv
        subst vs
        intro i ρ v a hd hVal hAt
        change At (.cons (.marked f d bs es) (ownerCopies f bs es ds)) i a at hAt
        cases hAt with
        | here =>
          have heq : d = ρ := by simpa using hd
          have hveq : cd = v := by simpa using hVal
          subst ρ
          subst v
          exact hM (f,d,Γ,cs,xs) cd bs es
            (ProtectedSpineSoundOwnerProof.retype F f τ d Γ cs xs bs es ho (ht d List.mem_cons_self)) he
        | there hAt =>
          exact ih tail (fun ρ hr => ht ρ (List.mem_cons_of_mem _ hr)) hTail
            _ _ _ _ (by simpa using hd) (by simpa using hVal) hAt

theorem select (F : Inputs S) (M : Code) (f : Head) (τ : Ty) (Γ : Context)
    (cs : List Code) (xs : List MarkedExtras.Tagged) (bs es : Args) (t : Expr)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (ho : OwnerRelated F (f,τ,Γ,cs,xs) bs es) (hM : FamilyRelated F M)
    (hObs : t ∈ observations F.data.names F.data.ports Γ F.target τ)
    (h : SelectWitness (domain F) F.data.sourceHeads M (f,τ,Γ,cs,xs) t) :
    Weak S (.marked f τ bs es) t := by
  let p : Parameter := (f,τ,Γ,cs,xs)
  obtain ⟨a,ha,hSelect⟩ := h
  have hSelected : ∃ i q, (At bs i q ∨ At es i q) ∧ a.1 = q.type ∧ Related F a.1 Γ a.2 (some q) := by
    rcases List.mem_append.mp ha with hb | he
    · obtain ⟨i,q,hi,ht,hr⟩ := ProtectedSpineSoundListProof.baseMember F Γ ho.2.2.2.1 hb
      exact ⟨i,q,Or.inl hi,ht,hr⟩
    · obtain ⟨i,q,hi,ht,hr⟩ := ho.2.2.2.2 a he
      exact ⟨i,q,Or.inr hi,ht,hr⟩
  obtain ⟨i,q,hAt,hAnn,hRelated⟩ := hSelected
  have hw := ho.1.2.2.1
  have ht := ProtectedSpineSoundBitProof.observedPaper F Γ τ t hObs
  have hTObs : Observed F Γ t := by
    unfold Observed
    rw [SpineShiftProof.annotationExact _ _ _ ht.1]
    exact hObs
  have hq : Typed EmptyContext q q.type := by
    have hTyped := ho.2.1.1
    cases hTyped with
    | marked hb he =>
      exact hAt.elim (fun h => ProtectedSpineSoundSourceProof.atTyped h
        (DecisionOccurrenceProof.baseExtras _ _ _ hb)) (fun h => ProtectedSpineSoundSourceProof.atTyped h he)
  rcases hSelect with ⟨hTy,hbit⟩ | ⟨ds,vs,hpre,hvs,hbit⟩
  · have he : q.type = ArrowPrefix [] τ := hAnn.symm.trans hTy
    exact .select ho.2.1 ht hAt (he ▸ hq) (show apply q (ownerCopies f bs es []) = some q from rfl)
      (ProtectedSpineSoundBitProof.tagged F Γ q t a hw hTObs hRelated false hbit)
  · have he : ArrowPrefix ds τ = q.type := ((FinitePrefixProof.forward _ _ _ hpre).2).trans hAnn
    have hqt : Typed EmptyContext q (ArrowPrefix ds τ) := he.symm ▸ hq
    have hSub := DecisionClosureCallProof.selection S F Γ f τ bs es t q i ds
      ho.2.1 ht hAt hqt ⟨hw,ho.2.2.1,hTObs⟩
    have haTy : a.1 ∈ F.data.types := hAnn.symm ▸ DecisionSourceBasicProof.rootType _ _ _ _ _ hSub.2.1
    have hDS := (ProtectedSpineAdequacyBase.prefixClosed S F a.1 haTy ds τ hpre).2
    obtain ⟨vs',hc,hv⟩ := MarkedConstructorSourceTupleProof.ownerTupleSuccess (domain F)
      F.data.sourceHeads M p hm ho.1 ds hDS
    have hvsEq : vs' = vs := Option.some.inj (hc.symm.trans hvs)
    subst vs'
    let out := StructuralActions.fullAction (domain F) a.1 Γ a.2 ds τ vs
    have hCall : CallTyped EmptyContext a.1 (ownerCopies f bs es ds) τ :=
      (FinitePrefixProof.forward _ _ _ hpre).2 ▸ hSub.2.2.2.2.2.2.2
    rw [Related.eq_def] at hRelated
    have hR : Related F τ Γ out (apply q (ownerCopies f bs es ds)) :=
      (hRelated.2 Γ hw (DecisionPortsProof.extensionRefl Γ)).2 ds τ hpre vs _ hv hCall
        hSub.2.2.1 (ownerTupleRelated F M f τ Γ cs xs bs es ds vs ho hM hDS hvs)
    cases hApp : apply q (ownerCopies f bs es ds) with
    | none =>
      rw [hApp] at hR
      have hFalse := ProtectedSpineSoundBitProof.undefinedWeak F Γ τ t out hw hObs hR
      exact Bool.noConfusion (hFalse.symm.trans hbit)
    | some r =>
      rw [hApp] at hR
      exact .select ho.2.1 ht hAt hqt hApp ((ProtectedSpineSoundBitProof.bits F Γ τ r t out hw hObs hR).1 hbit)

end LogicLineages.PersistentMarking.ProtectedSpineSoundSelectProof
