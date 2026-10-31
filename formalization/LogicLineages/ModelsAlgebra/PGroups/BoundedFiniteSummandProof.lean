module
public import LogicLineages.ModelsAlgebra.PGroups.BoundedFiniteSummandTargets
public import LogicLineages.ModelsAlgebra.PGroups.CyclicDecomposition
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary

theorem bounded_finite_summand : Targets.boundedFiniteSummand := by
  classical
  intro p _ G _ N hN B _ x
  obtain ⟨I,⟨e⟩⟩ := bounded_cyclic_decomposition p G N hN
  let J := Σ l : Fin N, I l
  letI : Fintype B := Fintype.ofFinite B
  let F : Finset J := (Finset.univ.biUnion (fun b : B => (e b).support)) ∪ (e x).support
  let K : AddSubgroup G :=
    { carrier := {a | ∀ i : J, i ∉ F → e a i = 0}
      zero_mem' := by intro i hi; simp
      add_mem' := by intro a b ha hb i hi; simp only [map_add,DFinsupp.add_apply,ha i hi,hb i hi,add_zero]
      neg_mem' := by intro a ha i hi; simp only [map_neg,DFinsupp.neg_apply,ha i hi,neg_zero] }
  let T : AddSubgroup G :=
    { carrier := {a | ∀ i : J, i ∈ F → e a i = 0}
      zero_mem' := by intro i hi; simp
      add_mem' := by intro a b ha hb i hi; simp only [map_add,DFinsupp.add_apply,ha i hi,hb i hi,add_zero]
      neg_mem' := by intro a ha i hi; simp only [map_neg,DFinsupp.neg_apply,ha i hi,neg_zero] }
  have hfinite : Finite K := by
    letI (i : J) : NeZero (p^(i.1.val+1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    let j : K → ∀ i : F, ZMod (p^(i.val.1.val+1)) := fun a i => e a i.val
    apply Finite.of_injective j
    intro a b hab
    apply Subtype.ext
    apply e.injective
    ext i
    by_cases hi : i ∈ F
    · exact congrFun hab ⟨i,hi⟩
    · exact (a.property i hi).trans (b.property i hi).symm
  have hB : B ≤ K := by
    intro b hb i hi
    by_contra hn
    apply hi
    apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨⟨b,hb⟩,Finset.mem_univ _,DFinsupp.mem_support_iff.mpr hn⟩
  have hx : x ∈ K := by
    intro i hi
    by_contra hn
    exact hi (Finset.mem_union_right _ (DFinsupp.mem_support_iff.mpr hn))
  have hd : Disjoint K T := by
    apply disjoint_iff_inf_le.mpr
    intro a ha
    change a=0
    apply e.injective
    ext i
    simp only [map_zero,DFinsupp.zero_apply]
    by_cases hi : i ∈ F
    · exact ha.2 i hi
    · exact ha.1 i hi
  have hs : K ⊔ T = ⊤ := by
    apply top_unique
    intro a _
    let b := (e a).filter (fun i => i ∈ F)
    let c := (e a).filter (fun i => i ∉ F)
    apply AddSubgroup.mem_sup.mpr
    refine ⟨e.symm b,?_,e.symm c,?_,?_⟩
    · intro i hi
      simp only [AddEquiv.apply_symm_apply,b,DFinsupp.filter_apply,if_neg hi]
    · intro i hi
      simp only [AddEquiv.apply_symm_apply,c,DFinsupp.filter_apply,not_true_eq_false,hi,if_false]
    · apply e.injective
      simpa only [map_add,AddEquiv.apply_symm_apply,b,c] using
        (DFinsupp.filter_add_filter_not (e a) (fun i => i ∈ F))
  exact ⟨K,T,hfinite,hB,hx,hd,hs⟩
end LogicLineages.ModelsAlgebra.PGroups
