module
public import LogicLineages.ModelsAlgebra.PGroups.PPrimaryFiniteGenerationTargets
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Data.Fin.Tuple.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u

private theorem finite_sup (G : Type u) [AddCommGroup G]
    (B C : AddSubgroup G) [Finite B] [Finite C] : Finite ↥(B ⊔ C) := by
  let a : B × C → ↥(B ⊔ C) := fun y =>
    ⟨(y.1:G)+y.2,AddSubgroup.add_mem_sup y.1.property y.2.property⟩
  have ha : Function.Surjective a := by
    intro y
    obtain ⟨b,c,hbc⟩ := AddSubgroup.mem_sup'.mp y.property
    exact ⟨(b,c),Subtype.ext hbc⟩
  exact Finite.of_surjective a ha

theorem p_primary_finite_tuple_extension : Targets.pPrimaryFiniteTupleExtension.{u} := by
  intro G _ p hp hG B _ n d
  have hcyclic (x : G) : Finite (AddSubgroup.zmultiples x) := by
    obtain ⟨k,hk⟩ := hG x
    have hxfin : IsOfFinAddOrder x := isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨p^k,pow_pos (Nat.pos_of_ne_zero hp) k,hk⟩
    exact hxfin.finite_zmultiples.to_subtype
  have hclosure : ∀ n : ℕ, ∀ d : Fin n → G, Finite (AddSubgroup.closure (Set.range d)) := by
    intro n
    induction n with
    | zero =>
      intro d
      have he : Set.range d = ∅ := by ext x; simp
      rw [he,AddSubgroup.closure_empty]
      infer_instance
    | succ n ih =>
      intro d
      letI := ih (Fin.tail d)
      letI := hcyclic (d 0)
      rw [Fin.range_fin_succ,Set.insert_eq,AddSubgroup.closure_union,
        ← AddSubgroup.zmultiples_eq_closure]
      exact finite_sup G _ _
  letI := hclosure n d
  exact finite_sup G B _

theorem p_primary_finite_tuple_closure : Targets.pPrimaryFiniteTupleClosure.{u} := by
  intro G _ p hp hG n d
  simpa only [bot_sup_eq] using p_primary_finite_tuple_extension G p hp hG ⊥ n d

end LogicLineages.ModelsAlgebra.PGroups
