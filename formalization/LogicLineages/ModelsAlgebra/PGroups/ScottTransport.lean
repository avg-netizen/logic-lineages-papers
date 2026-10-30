module

public import LogicLineages.ModelsAlgebra.PGroups.ScottTransportTargets
public import LogicLineages.ModelsAlgebra.PGroups.FullShift
public import LogicLineages.ModelsAlgebra.PGroups.TorsionScott
public import LogicLineages.ModelsAlgebra.PGroups.BackForthCore

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u v

theorem pi_scott_isomorphism : Targets.groupPiScottIsomorphism.{u,v} := by
  intro α G H _ _ e φ hφ
  have transfer : ∀ (A B : Type u) [AddCommGroup A] [AddCommGroup B]
      (f : A ≃+ B), φ.Realize (Fin.elim0 : Fin 0 → A) →
      φ.Realize (Fin.elim0 : Fin 0 → B) := by
    intro A B _ _ f ht
    have he : (fun j : Fin 0 => f (Fin.elim0 j)) = (Fin.elim0 : Fin 0 → B) := by
      funext j
      exact Fin.elim0 j
    have hc := GroupBackAndForth.comparison_isomorphism α A B f 0 Fin.elim0
    simpa only [he] using (truth_transfer α A B 0 Fin.elim0 _ hc).1 φ hφ ht
  constructor
  · intro hs
    refine ⟨transfer G H e hs.1, ?_⟩
    intro K _ _ ht
    obtain ⟨f⟩ := hs.2 K ht
    exact ⟨e.symm.trans f⟩
  · intro hs
    refine ⟨transfer H G e.symm hs.1, ?_⟩
    intro K _ _ ht
    obtain ⟨f⟩ := hs.2 K ht
    exact ⟨e.trans f⟩

theorem full_shift_no_sigma_two_scott : Targets.groupFullShiftNoSigmaTwoScott.{v} := by
  intro p _ k t ℓ h s r hk φ hφ
  letI : Countable (FullShiftGroup p k t ℓ s r) := full_shift_countable p k t ℓ s r
  letI : Infinite (FullShiftGroup p k t ℓ s r) := full_shift_infinite p k t ℓ s r hk
  apply p_primary_no_sigma_two_scott p (Fact.out : p.Prime) (FullShiftGroup p k t ℓ s r)
    (fun x => ⟨fullExponentBound k s r, full_shift_exponent p k t ℓ h s r x⟩) φ hφ

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
