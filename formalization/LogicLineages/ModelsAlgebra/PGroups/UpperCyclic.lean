module

public import LogicLineages.ModelsAlgebra.PGroups.UpperCyclicTargets
public import LogicLineages.ModelsAlgebra.PGroups.PowerCyclic
public import Mathlib.Algebra.Field.ZMod

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem upper_cyclic_finite : Targets.groupUpperCyclicFinite := by
  intro p _ s r
  infer_instance

theorem upper_cyclic_annihilation : Targets.groupUpperCyclicAnnihilation := by
  intro p s N r hr x
  funext a
  exact power_cyclic_annihilation p (r a) N (hr a) (x a)

theorem upper_cyclic_socle_roots : Targets.groupUpperCyclicSocleRoots := by
  classical
  intro p _ k s hk r hr x hx
  have hzero (a : Fin s) : p • x a = 0 := congrFun hx a
  choose z hz using fun a : Fin s =>
    power_cyclic_socle_roots p (r a) (lt_of_lt_of_le hk (hr a)) (x a) (hzero a)
  refine ⟨fun a => p ^ (r a - k) • z a, ?_⟩
  funext a
  change p ^ (k - 1) • (p ^ (r a - k) • z a) = x a
  have hs : r a - k + (k - 1) = r a - 1 := by have := hr a; omega
  rw [← mul_nsmul, ← pow_add, hs]
  exact hz a

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
