module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleExtensionTargets
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.GroupTheory.Divisible
public import Mathlib.RingTheory.PrincipalIdealDomain
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem integer_baer (A : Type) [AddCommGroup A] [DivisibleBy A ℤ] :
    Module.Baer ℤ A := fun I g => by
  rcases IsPrincipalIdealRing.principal I with ⟨m,rfl⟩
  obtain rfl | h0 := eq_or_ne m 0
  · refine ⟨0,fun n hn => ?_⟩
    rw [Submodule.span_zero_singleton] at hn
    subst hn
    exact (map_zero g).symm
  let gm := g ⟨m,Submodule.subset_span (Set.mem_singleton _)⟩
  refine ⟨LinearMap.toSpanSingleton ℤ A (DivisibleBy.div gm m),fun n hn => ?_⟩
  rcases Submodule.mem_span_singleton.mp hn with ⟨n,rfl⟩
  rw [map_zsmul,LinearMap.toSpanSingleton_apply,DivisibleBy.div_cancel gm h0,
    ← map_zsmul g,SetLike.mk_smul_mk]

theorem divisible_hom_extension : Targets.divisibleHomExtension := by
  classical
  intro G D _ _ hD S f
  letI : DivisibleBy D ℕ := divisibleByOfSMulRightSurj D ℕ (fun {n} hn => hD n hn)
  letI : DivisibleBy D ℤ := AddGroup.divisibleByIntOfDivisibleByNat D
  letI : Module.Injective ℤ D := (integer_baer D).injective
  obtain ⟨g,hg⟩ := Module.Injective.out (R := ℤ) (Q := D)
    S.subtype.toIntLinearMap Subtype.val_injective f.toIntLinearMap
  exact ⟨g.toAddMonoidHom,hg⟩
end LogicLineages.ModelsAlgebra.PGroups
