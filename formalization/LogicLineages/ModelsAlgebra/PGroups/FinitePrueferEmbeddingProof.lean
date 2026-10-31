module
public import LogicLineages.ModelsAlgebra.PGroups.FinitePrueferEmbeddingTargets
public import LogicLineages.ModelsAlgebra.PGroups.PrueferCyclicEmbeddingProof
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleExtensionProof
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem primary_pruefer_separation : Targets.primaryPrueferSeparation := by
  classical
  intro p _ G _ hp x hx
  obtain ⟨k,hk⟩ := hp x
  obtain ⟨l,_,hl⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
    ((addOrderOf_dvd_iff_nsmul_eq_zero).mpr hk)
  have hl0 : l ≠ 0 := by
    intro h
    have ho : addOrderOf x = 1 := by simpa [h] using hl
    exact hx (AddMonoid.addOrderOf_eq_one_iff.mp ho)
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl0
  let S := AddSubgroup.zmultiples x
  let s : S := ⟨x,AddSubgroup.mem_zmultiples x⟩
  have hg : ∀ z : S, z ∈ AddSubgroup.zmultiples s := by
    intro z
    obtain ⟨a,ha⟩ := z.property
    exact ⟨a,Subtype.ext ha⟩
  have hc : Nat.card S = p^(j+1) := (Nat.card_zmultiples x).trans hl
  let e : ZMod (p^(j+1)) ≃+ S := zmodAddEquivOfGenerator hg hc
  obtain ⟨i,hi⟩ := pruefer_cyclic_embedding p j
  let f : S →+ PrueferModel p := i.comp e.symm.toAddMonoidHom
  have hf : f s ≠ 0 := by
    intro hz
    have he : e.symm s = 0 := hi (hz.trans i.map_zero.symm)
    have hs : s = 0 := e.symm.injective (he.trans e.symm.map_zero.symm)
    exact hx (congrArg Subtype.val hs)
  obtain ⟨g,hg⟩ := divisible_hom_extension G (PrueferModel p)
    (genuine_pruefer_model p).2.1 S f
  refine ⟨g,?_⟩
  change g (s:G) ≠ 0
  rw [hg]
  exact hf

theorem finite_pruefer_embedding : Targets.finitePrueferEmbedding := by
  classical
  intro p _ G _ _ hp
  letI := Fintype.ofFinite G
  have hchars : ∀ x : G, ∃ f : G →+ PrueferModel p, x ≠ 0 → f x ≠ 0 := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0,fun h => (h hx).elim⟩
    · obtain ⟨f,hf⟩ := primary_pruefer_separation p G hp x hx
      exact ⟨f,fun _ => hf⟩
  choose c hc using hchars
  let e := Fintype.equivFin G
  let f : G →+ (Fin (Fintype.card G) → PrueferModel p) :=
    { toFun := fun x j => c (e.symm j) x
      map_zero' := funext (fun j => (c (e.symm j)).map_zero)
      map_add' := fun x y => funext (fun j => (c (e.symm j)).map_add x y) }
  refine ⟨Fintype.card G,f,?_⟩
  intro a b hab
  by_contra hne
  have hn : a-b ≠ 0 := sub_ne_zero.mpr hne
  apply hc (a-b) hn
  have hh := congrFun hab (e (a-b))
  change c (e.symm (e (a-b))) a = c (e.symm (e (a-b))) b at hh
  rw [e.symm_apply_apply] at hh
  rw [map_sub,hh,sub_self]
end LogicLineages.ModelsAlgebra.PGroups
