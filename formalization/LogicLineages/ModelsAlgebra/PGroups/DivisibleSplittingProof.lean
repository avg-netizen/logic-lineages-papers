module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleSplittingTargets
public import LogicLineages.ModelsAlgebra.PGroups.DivisiblePartProof
public import LogicLineages.ModelsAlgebra.PGroups.SubgroupSumProductProof
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

theorem divisible_subgroup_retraction : Targets.divisibleSubgroupRetraction := by
  classical
  intro G _ D hD
  letI : DivisibleBy D ℕ := divisibleByOfSMulRightSurj D ℕ (fun {n} hn => hD n hn)
  letI : DivisibleBy D ℤ := AddGroup.divisibleByIntOfDivisibleByNat D
  letI : Module.Injective ℤ D := (integer_baer D).injective
  obtain ⟨r,hr⟩ := Module.Injective.out (R := ℤ) (Q := D)
    D.subtype.toIntLinearMap Subtype.val_injective (LinearMap.id : D →ₗ[ℤ] D)
  exact ⟨r.toAddMonoidHom,hr⟩

theorem actual_divisible_splitting : Targets.actualDivisibleSplitting := by
  classical
  intro G _
  obtain ⟨r,hr⟩ := divisible_subgroup_retraction G (divisiblePart G) (actual_divisible_part G).1
  let R : AddSubgroup G := r.ker
  have hd : Disjoint R (divisiblePart G) := by
    apply AddSubgroup.disjoint_def.mpr
    intro x hx hxD
    have hz : r x = 0 := hx
    have he := hr ⟨x,hxD⟩
    exact congrArg (fun z : divisiblePart G => (z:G)) (he.symm.trans hz)
  have hs : R ⊔ divisiblePart G = ⊤ := by
    apply le_antisymm le_top
    intro x _
    apply AddSubgroup.mem_sup.mpr
    refine ⟨x-(r x:G),?_,(r x:G),(r x).property,sub_add_cancel _ _⟩
    change r (x-(r x:G)) = 0
    rw [map_sub,hr,sub_self]
  have hred : IsReducedAddGroup R := by
    intro S hS
    let U : AddSubgroup G := S.map R.subtype
    have hU : SubgroupDivisible U := by
      intro n hn x
      obtain ⟨a,ha,he⟩ := x.property
      obtain ⟨b,hb⟩ := hS n hn ⟨a,ha⟩
      refine ⟨⟨(b:R),⟨(b:R),b.property,rfl⟩⟩,Subtype.ext ?_⟩
      change n • ((b:R):G) = (x:G)
      have hh := congrArg (fun z : S => ((z:R):G)) hb
      exact hh.trans he
    have hle := (actual_divisible_part G).2 U hU
    apply le_antisymm _ bot_le
    intro x hx
    have hxD : (x:G) ∈ divisiblePart G := hle ⟨x,hx,rfl⟩
    exact Subtype.ext (AddSubgroup.disjoint_def.mp hd x.property hxD)
  obtain ⟨e,he⟩ := subgroup_sum_product G ⊤ R (divisiblePart G) hs.symm hd
  refine ⟨r,R,hr,rfl,hred,hd,hs,e.trans (AddSubgroup.topEquiv : (⊤ : AddSubgroup G) ≃+ G),?_⟩
  exact he
end LogicLineages.ModelsAlgebra.PGroups
