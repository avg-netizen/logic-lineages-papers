module
public import LogicLineages.ModelsAlgebra.PGroups.PrimeExtensionKernelTargets
public import LogicLineages.ModelsAlgebra.PGroups.PrimeCoset
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u

theorem prime_extension_kernel : Targets.groupPrimeExtensionKernel.{u} := by
  intro G H _ _ p _ B x hx hpx f hf w hw hpw
  let px : B := ⟨p • x,hpx⟩
  have relation (b : B) (z : ℤ) (hz : (p : ℤ) ∣ z) :
      (b : G) + z • x = 0 ↔ f b + z • w = 0 := by
    obtain ⟨k,rfl⟩ := hz
    have hxk : ((p : ℤ) * k) • x = k • (p • x) := by
      rw [Int.mul_comm, mul_smul, natCast_zsmul]
    have hwk : ((p : ℤ) * k) • w = k • (p • w) := by
      rw [Int.mul_comm, mul_smul, natCast_zsmul]
    rw [hxk, hwk, hpw, ← map_zsmul, ← map_add]
    change ((b + k • px : B) : G) = 0 ↔ f (b + k • px) = 0
    constructor
    · intro h
      have h0 : b + k • px = 0 := Subtype.ext h
      rw [h0, map_zero]
    · intro h
      have h0 : b + k • px = 0 := hf (h.trans (map_zero f).symm)
      exact congrArg (fun a : B => (a : G)) h0
  ext a
  rcases a with ⟨b,z⟩
  change (b : G) + z • x = 0 ↔ f b + z • w = 0
  constructor
  · intro h
    have hm : z • x ∈ B := by
      have hm0 : (b : G) + z • x ∈ B := h ▸ B.zero_mem
      simpa only [neg_add_cancel_left] using B.add_mem (B.neg_mem b.property) hm0
    exact (relation b z ((prime_coset_integer_membership G p B x hx hpx z).mp hm)).mp h
  · intro h
    have hwp : p • w ∈ f.range := hpw ▸ ⟨px,rfl⟩
    have hm : z • w ∈ f.range := by
      have hm0 : f b + z • w ∈ f.range := h ▸ f.range.zero_mem
      simpa only [neg_add_cancel_left] using f.range.add_mem (f.range.neg_mem ⟨b,rfl⟩) hm0
    exact (relation b z ((prime_coset_integer_membership H p f.range w hw hwp z).mp hm)).mpr h

end LogicLineages.ModelsAlgebra.PGroups
