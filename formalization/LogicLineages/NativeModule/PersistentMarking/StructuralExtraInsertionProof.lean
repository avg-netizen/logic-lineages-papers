module

public import LogicLineages.NativeModule.PersistentMarking.StructuralActionTargets
public import LogicLineages.NativeModule.PersistentMarking.MarkedExtrasWeakeningProof

@[expose] public section

namespace LogicLineages.PersistentMarking.StructuralExtraInsertionProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedExtras

theorem valid : StructuralActionTargets.ExtraInsertionValid := by
  intro E Γ es xs hw hes hxs
  apply MarkedExtrasDownProof.downExtra E Γ (es ++ xs) hw
  intro x hx
  rcases List.mem_append.mp hx with he | hx
  · exact MarkedExtrasDownProof.canonicalMember E Γ es hes.1 x he
  · exact hxs x hx

theorem natural : StructuralActionTargets.ExtraInsertionNatural := by
  intro E Γ Δ es xs hw hd he hes hxs
  have hm := MarkedExtrasRestrictionProof.monotone E Γ Δ hw hd he
  have ho := MarkedExtrasFoundationProof.order E Δ hd
  have hs : ∀ a, a ∈ es ++ xs → a ∈ «universe» E Γ := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact MarkedExtrasDownProof.canonicalMember E Γ es hes.1 a ha
    · exact hxs a ha
  have hi := valid E Γ es xs hw hes hxs
  have hwes := MarkedExtrasRestrictionProof.weakening E Γ Δ es hw hd he hes
  have hmx : ∀ a, a ∈ xs.map (restricted E Γ Δ) → a ∈ «universe» E Δ := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    exact hm.1 x (hxs x hx)
  apply MarkedExtrasDownProof.canonicalExt E Δ _ _
    (MarkedExtrasRestrictionProof.weakening E Γ Δ _ hw hd he hi).1
    (valid E Δ _ _ hd hwes hmx).1
  intro b hb
  constructor
  · intro h
    obtain ⟨_,a,ha,hba⟩ := (MarkedExtrasWeakeningProof.weakeningMember E Γ Δ _ b).mp h
    obtain ⟨ham,z,hz,haz⟩ := (MarkedExtrasFoundationProof.downExact E Γ (es ++ xs) a).mp ha
    have hzm := hs z hz
    have hbz := ho.2.1 b (restricted E Γ Δ a) (restricted E Γ Δ z)
      hb (hm.1 a ham) (hm.1 z hzm) hba (hm.2 a z ham hzm haz)
    apply (MarkedExtrasFoundationProof.downExact E Δ _ b).mpr
    refine ⟨hb,restricted E Γ Δ z,?_,hbz⟩
    rcases List.mem_append.mp hz with hz | hz
    · apply List.mem_append.mpr; left
      exact (MarkedExtrasWeakeningProof.weakeningMember E Γ Δ es _).mpr
        ⟨hm.1 z hzm,z,hz,ho.1 _ (hm.1 z hzm)⟩
    · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨z,hz,rfl⟩))
  · intro h
    obtain ⟨_,a,ha,hba⟩ := (MarkedExtrasFoundationProof.downExact E Δ _ b).mp h
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨ham,z,hz,haz⟩ := (MarkedExtrasWeakeningProof.weakeningMember E Γ Δ es a).mp ha
      have hzm := hs z (List.mem_append.mpr (Or.inl hz))
      have hzdown : z ∈ StructuralActions.insertExtras E Γ es xs :=
        (MarkedExtrasFoundationProof.downExact E Γ _ z).mpr
          ⟨hzm,z,List.mem_append.mpr (Or.inl hz),(MarkedExtrasFoundationProof.order E Γ hw).1 z hzm⟩
      exact (MarkedExtrasWeakeningProof.weakeningMember E Γ Δ _ b).mpr
        ⟨hb,z,hzdown,ho.2.1 b a (restricted E Γ Δ z) hb ham (hm.1 z hzm) hba haz⟩
    · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
      have hzm := hxs z hz
      have hzdown : z ∈ StructuralActions.insertExtras E Γ es xs :=
        (MarkedExtrasFoundationProof.downExact E Γ _ z).mpr
          ⟨hzm,z,List.mem_append.mpr (Or.inr hz),(MarkedExtrasFoundationProof.order E Γ hw).1 z hzm⟩
      exact (MarkedExtrasWeakeningProof.weakeningMember E Γ Δ _ b).mpr ⟨hb,z,hzdown,hba⟩
end LogicLineages.PersistentMarking.StructuralExtraInsertionProof
