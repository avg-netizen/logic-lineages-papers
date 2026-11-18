import LogicLineages.PersistentMarking.MarkedFamilyOrderProof
import LogicLineages.PersistentMarking.HereditaryLatticeInductionProof
namespace LogicLineages.PersistentMarking.MarkedFamilyAggregateProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedFamilyParameters MarkedFamilyCoding MarkedFamilyCoherence

theorem members (E : Environment) (heads : List Head) (cs : List Code)
    (hc : ∀ c, c ∈ cs → c ∈ MarkedFamilyCoherence.retained E heads)
    (p : Parameter) (hp : MarkedFamilyParameters.Valid E heads p) :
    ∀ x, x ∈ cs.map (fun c => MarkedFamilyCoding.decode E heads c p) →
      x ∈ (descriptor E p.2.1).carriers p.2.2.1 := by
  intro x hx
  obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hx
  exact ((MarkedFamilyRetentionProof.retentionExact E heads c).mp (hc c hc')).2.1 p hp

theorem mapMono (E : Environment) (σ : Ty) (Γ : Context) (hw : WellFormed E.types E.ports Γ)
    (cs : List Code) (f g : Code → Code)
    (hf : ∀ c, c ∈ cs → f c ∈ (descriptor E σ).carriers Γ)
    (hg : ∀ c, c ∈ cs → g c ∈ (descriptor E σ).carriers Γ)
    (hfg : ∀ c, c ∈ cs → (descriptor E σ).le Γ (f c) (g c) = true) :
    (descriptor E σ).le Γ ((descriptor E σ).join Γ (cs.map f)) ((descriptor E σ).join Γ (cs.map g)) = true ∧
    (descriptor E σ).le Γ ((descriptor E σ).meet Γ (cs.map f)) ((descriptor E σ).meet Γ (cs.map g)) = true := by
  have hfm : ∀ x, x ∈ cs.map f → x ∈ (descriptor E σ).carriers Γ := by
    intro x hx; obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hx; exact hf c hc
  have hgm : ∀ x, x ∈ cs.map g → x ∈ (descriptor E σ).carriers Γ := by
    intro x hx; obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hx; exact hg c hc
  have jf := HereditaryLatticeInductionProof.join E σ Γ (cs.map f) hw hfm
  have jg := HereditaryLatticeInductionProof.join E σ Γ (cs.map g) hw hgm
  have mf := HereditaryLatticeInductionProof.meet E σ Γ (cs.map f) hw hfm
  have mg := HereditaryLatticeInductionProof.meet E σ Γ (cs.map g) hw hgm
  have trans := (HereditaryPartialOrderProof.partialOrder E σ Γ hw).2.1
  constructor
  · apply jf.2.2 _ jg.1
    intro x hx; obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hx
    exact trans _ _ _ (hf c hc) (hg c hc) jg.1 (hfg c hc) (jg.2.1 _ (List.mem_map.mpr ⟨c,hc,rfl⟩))
  · apply mg.2.2 _ mf.1
    intro x hx; obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hx
    exact trans _ _ _ mf.1 (hf c hc) (hg c hc) (mf.2.1 _ (List.mem_map.mpr ⟨c,hc,rfl⟩)) (hfg c hc)

theorem aggregateValid : MarkedFamilyLatticeTargets.AggregateValid := by
  intro isMeet E heads cs hc
  refine ⟨?_,?_,?_⟩
  · intro p hp
    have hm := members E heads cs hc p hp
    cases isMeet
    · exact (HereditaryLatticeInductionProof.join E p.2.1 p.2.2.1 _ hp.2.2.1 hm).1
    · exact (HereditaryLatticeInductionProof.meet E p.2.1 p.2.2.1 _ hp.2.2.1 hm).1
  · intro p q hp hq hle
    have ht := hle.2.1
    have hg := hle.2.2.1
    have hpm : ∀ c, c ∈ cs → MarkedFamilyCoding.decode E heads c p ∈ (descriptor E p.2.1).carriers p.2.2.1 := by
      intro c h; exact ((MarkedFamilyRetentionProof.retentionExact E heads c).mp (hc c h)).2.1 p hp
    have hqm : ∀ c, c ∈ cs → MarkedFamilyCoding.decode E heads c q ∈ (descriptor E p.2.1).carriers p.2.2.1 := by
      intro c h; rw [ht,hg]; exact ((MarkedFamilyRetentionProof.retentionExact E heads c).mp (hc c h)).2.1 q hq
    have hh := mapMono E p.2.1 p.2.2.1 hp.2.2.1 cs
      (fun c => MarkedFamilyCoding.decode E heads c p) (fun c => MarkedFamilyCoding.decode E heads c q) hpm hqm
      (fun c h => ((MarkedFamilyRetentionProof.retentionExact E heads c).mp (hc c h)).2.2.1 p q hp hq hle)
    cases isMeet <;> simp only [MarkedFamilyLattice.aggregate,Bool.false_eq_true,if_false,if_true]
    · simpa only [←ht,←hg] using hh.1
    · simpa only [←ht,←hg] using hh.2
  · intro p hp Δ hw he
    have hm := members E heads cs hc p hp
    have hr := HereditaryLatticeInductionProof.restriction E p.2.1 p.2.2.1 Δ _ hp.2.2.1 hw he hm
    have hmap : (cs.map (fun c => MarkedFamilyCoding.decode E heads c p)).map ((descriptor E p.2.1).restrict p.2.2.1 Δ) =
        cs.map (fun c => MarkedFamilyCoding.decode E heads c (weakenParameter E p Δ)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro c h
      exact ((MarkedFamilyRetentionProof.retentionExact E heads c).mp (hc c h)).2.2.2 p hp Δ hw he
    cases isMeet <;> simp only [MarkedFamilyLattice.aggregate,Bool.false_eq_true,if_false,if_true,weakenParameter]
    · exact hr.1.trans (congrArg ((descriptor E p.2.1).join Δ) hmap)
    · exact hr.2.trans (congrArg ((descriptor E p.2.1).meet Δ) hmap)
end LogicLineages.PersistentMarking.MarkedFamilyAggregateProof
