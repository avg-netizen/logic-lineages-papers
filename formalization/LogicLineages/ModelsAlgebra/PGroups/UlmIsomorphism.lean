module

public import LogicLineages.ModelsAlgebra.PGroups.UlmMapDefinitions

@[expose] public section

/-!
# The local Ulm isomorphism by explicit kernel correction

The argument follows the second paragraph of paper 01's quotient-
filtration proof. Its target is bijectivity of the constructed map,
not existence of an unrelated isomorphism or a supplied bijection.
-/

namespace LogicLineages.ModelsAlgebra.PGroups.UlmLocal

variable {G : Type*} {H : Type*} [AddCommGroup G] [AddCommGroup H]

theorem step_le (p : ℕ) (S : AddSubgroup G) : pStep p S ≤ S := by
  rintro x ⟨y, hy, rfl⟩
  exact S.nsmul_mem hy p

theorem nextSocle_le (p : ℕ) (S : AddSubgroup G) :
    pSocle p (pStep p S) ≤ pSocle p S := by
  intro x hx
  exact ⟨step_le p S hx.1, hx.2⟩

theorem mem_successor_iff (p : ℕ) (S : AddSubgroup G) (x : pSocle p S) :
    x ∈ successorSocleSubgroup p S ↔ (x : G) ∈ pStep p S :=
  ⟨fun h => h.1, fun h => ⟨h, x.property.2⟩⟩

theorem preimage_successor (p : ℕ) (S : AddSubgroup G) (f : G →+ H)
    (hdeep : f.ker ≤ pStep p (pStep p S)) :
    (successorSocleSubgroup p (S.map f)).comap (pSocleMap p S f) =
      successorSocleSubgroup p S := by
  apply le_antisymm
  · intro x hx
    have hfx : f (x : G) ∈ pStep p (S.map f) :=
      (mem_successor_iff p (S.map f) (pSocleMap p S f x)).mp hx
    rw [← map_pStep p f S] at hfx
    obtain ⟨z, hz, heq⟩ := hfx
    have hker : (x : G) - z ∈ f.ker := by
      change f ((x : G) - z) = 0
      rw [map_sub, heq, sub_self]
    have hdiff : (x : G) - z ∈ pStep p S :=
      step_le p (pStep p S) (hdeep hker)
    apply (mem_successor_iff p S x).mpr
    simpa only [sub_add_cancel] using (pStep p S).add_mem hdiff hz
  · exact pSocleMap_successor p S f

theorem ulmMap_injective (p : ℕ) (S : AddSubgroup G) (f : G →+ H)
    (hdeep : f.ker ≤ pStep p (pStep p S)) : Function.Injective (ulmMap p S f) := by
  let q : UlmLayer p S →+ UlmLayer p (S.map f) :=
    QuotientAddGroup.map (successorSocleSubgroup p S)
      (successorSocleSubgroup p (S.map f)) (pSocleMap p S f)
      (pSocleMap_successor p S f)
  change Function.Injective q
  apply (AddMonoidHom.ker_eq_bot_iff q).mp
  change (QuotientAddGroup.map (successorSocleSubgroup p S)
    (successorSocleSubgroup p (S.map f)) (pSocleMap p S f)
    (pSocleMap_successor p S f)).ker = ⊥
  rw [QuotientAddGroup.ker_map, preimage_successor p S f hdeep,
    QuotientAddGroup.map_mk'_self]

theorem ulmMap_surjective (p : ℕ) (S : AddSubgroup G) (f : G →+ H)
    (hdeep : f.ker ≤ pStep p (pStep p S)) : Function.Surjective (ulmMap p S f) := by
  intro y
  obtain ⟨a, rfl⟩ :=
    QuotientAddGroup.mk'_surjective (successorSocleSubgroup p (S.map f)) y
  obtain ⟨x, hx, hfx⟩ := a.property.1
  have hpx : p • x ∈ f.ker := by
    change f (p • x) = 0
    rw [map_nsmul, hfx]
    exact a.property.2
  obtain ⟨z, hz, hpz⟩ := hdeep hpx
  change p • z = p • x at hpz
  let w : pSocle p S := ⟨x - z, ⟨S.sub_mem hx (step_le p S hz), by
    change p • (x - z) = 0
    rw [nsmul_sub, ← hpz, sub_self]⟩⟩
  let b : pSocle p (S.map f) := pSocleMap p S f w
  have hdiff : (b : H) - (a : H) = -f z := by
    change f (x - z) - (a : H) = -f z
    rw [map_sub, hfx, sub_right_comm, sub_self, zero_sub]
  have hzfilt : f z ∈ pStep p (S.map f) := by
    rw [← map_pStep p f S]
    exact ⟨z, hz, rfl⟩
  have hba : b - a ∈ successorSocleSubgroup p (S.map f) := by
    apply (mem_successor_iff p (S.map f) (b - a)).mpr
    change (b : H) - (a : H) ∈ pStep p (S.map f)
    rw [hdiff]
    exact (pStep p (S.map f)).neg_mem hzfilt
  refine ⟨QuotientAddGroup.mk' (successorSocleSubgroup p S) w, ?_⟩
  rw [ulmMap_mk]
  exact QuotientAddGroup.eq_iff_sub_mem.mpr hba

theorem ulmMap_bijective (p : ℕ) (S : AddSubgroup G) (f : G →+ H)
    (hdeep : f.ker ≤ pStep p (pStep p S)) : Function.Bijective (ulmMap p S f) :=
  ⟨ulmMap_injective p S f hdeep, ulmMap_surjective p S f hdeep⟩

end LogicLineages.ModelsAlgebra.PGroups.UlmLocal
