module
public import LogicLineages.ModelsAlgebra.PGroups.PrimeExtensionTargets
public import LogicLineages.ModelsAlgebra.PGroups.PrimeExtensionKernel
public import LogicLineages.ModelsAlgebra.PGroups.KernelFactorization
public import Mathlib.Algebra.Group.Submonoid.Operations
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u

theorem prime_order_extension : Targets.groupPrimeOrderExtension.{u} := by
  intro G H _ _ p _ B x hx hpx f hf w hw hpw
  let S := B ⊔ AddSubgroup.zmultiples x
  let s : B × ℤ →+ S := (adjunctionHom G B x).codRestrict S (by
    intro a
    exact AddSubgroup.add_mem_sup a.1.property
      (AddSubgroup.zsmul_mem_zmultiples x a.2))
  have hs : Function.Surjective s := by
    intro a
    obtain ⟨b,hb,y,hy,hby⟩ := AddSubgroup.mem_sup.mp a.property
    obtain ⟨z,rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    exact ⟨(⟨b,hb⟩,z),Subtype.ext hby⟩
  have hker : s.ker = (mappedAdjunctionHom G H B f w).ker := by
    rw [← prime_extension_kernel G H p B x hx hpx f hf w hw hpw]
    ext a
    change s a = 0 ↔ (adjunctionHom G B x) a = 0
    constructor
    · intro h
      exact congrArg (fun z : S => (z : G)) h
    · intro h
      exact Subtype.ext h
  obtain ⟨F,hF,hval⟩ := kernel_factorization (B × ℤ) S H s
    (mappedAdjunctionHom G H B f w) hs hker
  refine ⟨F,hF,?_,?_⟩
  · intro b
    have h := hval (b,0)
    simpa [s,adjunctionHom,mappedAdjunctionHom,integerMultipleHom] using h
  · have h := hval (0,1)
    simpa [s,adjunctionHom,mappedAdjunctionHom,integerMultipleHom] using h

end LogicLineages.ModelsAlgebra.PGroups
