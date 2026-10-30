module
public import LogicLineages.ModelsAlgebra.PGroups.ProperExtensionTransportTargets
public import LogicLineages.ModelsAlgebra.PGroups.ProperCoset
public import Mathlib.Data.Int.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem proper_extension_transport : Targets.groupProperExtensionTransport.{u,v} := by
  intro G H _ _ p hp hG hH B x hpx f w α δ hpres hx hxnot hw hwnot hproper hwproper F hFb hFx y β hβ
  let S := B ⊔ AddSubgroup.zmultiples x
  let xS : S := ⟨x,(le_sup_right : AddSubgroup.zmultiples x ≤ S) (AddSubgroup.mem_zmultiples x)⟩
  obtain ⟨b,hb,t,ht,hbt⟩ := AddSubgroup.mem_sup.mp y.property
  obtain ⟨z,rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp ht
  let bB : B := ⟨b,hb⟩
  let bS : S := ⟨b,(le_sup_left : B ≤ S) hb⟩
  have hy : y = bS + z • xS := Subtype.ext hbt.symm
  by_cases hz : (p : ℤ) ∣ z
  · obtain ⟨k,hk⟩ := hz
    have hzmem : z • x ∈ B := by
      rw [hk, Int.mul_comm, mul_smul, natCast_zsmul]
      exact B.zsmul_mem hpx k
    have hyB : (y:G) ∈ B := by
      rw [← hbt]
      exact B.add_mem hb hzmem
    have he : F y = f ⟨y,hyB⟩ := hFb ⟨y,hyB⟩
    rw [he]
    exact hpres ⟨y,hyB⟩ β hβ
  · have hcop : Nat.Coprime z.natAbs p := by
      apply Nat.Coprime.symm
      apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      intro h
      exact hz (Int.natCast_dvd.mpr h)
    have hpH : ∀ c : f.range, ∀ γ : Ordinal.{v},
        w + c ∈ (transfiniteFiltration p γ : AddSubgroup H) →
        w ∈ (transfiniteFiltration p γ : AddSubgroup H) := by
      intro c γ hc
      obtain ⟨a,ha⟩ := c.property
      have hc' : w + f a ∈ (transfiniteFiltration p γ : AddSubgroup H) := by
        simpa only [ha] using hc
      exact hwproper a γ hc'
    have hsame : w ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
        x ∈ (transfiniteFiltration p β : AddSubgroup G) := by
      by_cases hβα : β ≤ α
      · exact ⟨fun _ => transfiniteFiltration_antitone p hβα hx,
          fun _ => transfiniteFiltration_antitone p hβα hw⟩
      · have hab : α+1 ≤ β := Order.succ_le_of_lt (lt_of_not_ge hβα)
        exact ⟨fun h => False.elim (hwnot (transfiniteFiltration_antitone p hab h)),
          fun h => False.elim (hxnot (transfiniteFiltration_antitone p hab h))⟩
    have hsrc := proper_coset_sum_membership G p hG B x hproper z hcop bB β
    have htgt := proper_coset_sum_membership H p hH f.range w hpH z hcop
      ⟨f bB,⟨bB,rfl⟩⟩ β
    have hval : F y = f bB + z • w := by
      rw [hy, map_add, map_zsmul]
      change F bS + z • F xS = f bB + z • w
      rw [hFb bB, hFx]
    have hco : (y:G) = b + z • x := hbt.symm
    rw [hval, hco, add_comm (f bB), add_comm b]
    change z • w + f bB ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
      z • x + (bB:G) ∈ (transfiniteFiltration p β : AddSubgroup G)
    rw [htgt, hsrc, hsame, hpres bB β hβ]

end LogicLineages.ModelsAlgebra.PGroups
