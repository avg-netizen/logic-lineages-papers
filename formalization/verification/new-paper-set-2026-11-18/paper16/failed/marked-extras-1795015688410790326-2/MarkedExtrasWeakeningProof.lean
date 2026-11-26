import LogicLineages.PersistentMarking.MarkedExtrasRestrictionProof
import LogicLineages.PersistentMarking.HereditaryRestrictionAlgebraProof
namespace LogicLineages.PersistentMarking.MarkedExtrasWeakeningProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedExtras

theorem restrictedIdentity (E : Environment) (Γ : Context) (a : Tagged)
    (hw : WellFormed E.types E.ports Γ) (ha : a ∈ universe E Γ) : restricted E Γ Γ a = a := by
  obtain ⟨σ,c⟩ := a
  have h := (HereditaryRestrictionAlgebraProof.algebra E σ).1 Γ c hw
    ((MarkedExtrasFoundationProof.universeExact E Γ σ c).mp ha).2
  exact congrArg (fun x => (σ,x)) h

theorem restrictedComposition (E : Environment) (Γ Δ Θ : Context) (a : Tagged)
    (hw : WellFormed E.types E.ports Γ) (hd : WellFormed E.types E.ports Δ)
    (ht : WellFormed E.types E.ports Θ) (he : Extends Γ Δ) (hf : Extends Δ Θ)
    (ha : a ∈ universe E Γ) : restricted E Δ Θ (restricted E Γ Δ a) = restricted E Γ Θ a := by
  obtain ⟨σ,c⟩ := a
  have h := (HereditaryRestrictionAlgebraProof.algebra E σ).2 Γ Δ Θ c hw hd ht he hf
    ((MarkedExtrasFoundationProof.universeExact E Γ σ c).mp ha).2
  exact congrArg (fun x => (σ,x)) h

theorem weakeningMember (E : Environment) (Γ Θ : Context) (xs : List Tagged) (b : Tagged) :
    b ∈ weaken E Γ Θ xs ↔ b ∈ universe E Θ ∧ ∃ a, a ∈ xs ∧ le E Θ b (restricted E Γ Θ a) = true := by
  rw [MarkedExtrasFoundationProof.downExact]
  constructor
  · rintro ⟨hb,a,ha,hba⟩
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    exact ⟨hb,x,hx,hba⟩
  · rintro ⟨hb,a,ha,hba⟩
    exact ⟨hb,restricted E Γ Θ a,List.mem_map.mpr ⟨a,ha,rfl⟩,hba⟩

theorem algebra : MarkedExtrasTargets.WeakeningAlgebra := by
  intro E
  constructor
  · intro Γ xs hw hx
    have hm : xs.map (restricted E Γ Γ) = xs := by
      rw [←List.map_id xs]
      apply List.map_congr_left
      intro a ha
      exact restrictedIdentity E Γ a hw (MarkedExtrasDownProof.canonicalMember E Γ xs hx.1 a ha)
    unfold weaken
    rw [hm]
    exact MarkedExtrasDownProof.downIdentity E Γ xs hw hx
  · intro Γ Δ Θ xs hw hd ht he hf hx
    have hΓΘ := DecisionPortsProof.extensionTrans Γ Δ Θ he hf
    have hm := MarkedExtrasRestrictionProof.monotone E Γ Δ hw hd he
    have hn := MarkedExtrasRestrictionProof.monotone E Δ Θ hd ht hf
    have ho := MarkedExtrasFoundationProof.order E Θ ht
    have hweak := MarkedExtrasRestrictionProof.weakening E Γ Δ xs hw hd he hx
    apply MarkedExtrasDownProof.canonicalExt E Θ _ _
      (MarkedExtrasRestrictionProof.weakening E Δ Θ _ hd ht hf hweak).1
      (MarkedExtrasRestrictionProof.weakening E Γ Θ xs hw ht hΓΘ hx).1
    intro b hb
    constructor
    · intro h
      obtain ⟨_,a,ha,hba⟩ := (weakeningMember E Δ Θ _ b).mp h
      obtain ⟨ham,z,hz,haz⟩ := (weakeningMember E Γ Δ xs a).mp ha
      have hzm := MarkedExtrasDownProof.canonicalMember E Γ xs hx.1 z hz
      have hrz := hm.1 z hzm
      have hle := hn.2 a (restricted E Γ Δ z) ham hrz haz
      have hcomp := restrictedComposition E Γ Δ Θ z hw hd ht he hf hzm
      rw [hcomp] at hle
      exact (weakeningMember E Γ Θ xs b).mpr ⟨hb,z,hz,
        ho.2.1 b (restricted E Δ Θ a) (restricted E Γ Θ z) hb (hn.1 a ham)
          ((MarkedExtrasRestrictionProof.monotone E Γ Θ hw ht hΓΘ).1 z hzm) hba hle⟩
    · intro h
      obtain ⟨_,z,hz,hbz⟩ := (weakeningMember E Γ Θ xs b).mp h
      have hzm := MarkedExtrasDownProof.canonicalMember E Γ xs hx.1 z hz
      have hrz := hm.1 z hzm
      have ha : restricted E Γ Δ z ∈ weaken E Γ Δ xs :=
        (weakeningMember E Γ Δ xs _).mpr ⟨hrz,z,hz,(MarkedExtrasFoundationProof.order E Δ hd).1 _ hrz⟩
      apply (weakeningMember E Δ Θ _ b).mpr
      refine ⟨hb,restricted E Γ Δ z,ha,?_⟩
      rw [restrictedComposition E Γ Δ Θ z hw hd ht he hf hzm]
      exact hbz
end LogicLineages.PersistentMarking.MarkedExtrasWeakeningProof
