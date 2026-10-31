module
public import LogicLineages.ModelsAlgebra.PGroups.AtomicGeneratedIsoTargets
public import LogicLineages.ModelsAlgebra.PGroups.TermClosure
public import LogicLineages.ModelsAlgebra.PGroups.BackForthCore
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth
universe u

theorem atomic_generated_iso : Targets.atomicGeneratedIso.{u} := by
  classical
  intro G H _ _ n a b
  let A := AddSubgroup.closure (Set.range a)
  let B := AddSubgroup.closure (Set.range b)
  constructor
  · intro hab
    choose t ht using fun x : A => closure_term_representation G n a (x:G) x.property
    let f : A → B := fun x => ⟨(t x).eval b,term_closure_membership H n b (t x)⟩
    have hf (x : A) (s : GroupTerm n) (hs : s.eval a = (x:G)) :
        (f x : H) = s.eval b := (hab (t x) s).mp ((ht x).trans hs.symm)
    let F : A →+ B := {
      toFun := f
      map_zero' := Subtype.ext (hf 0 .zero rfl)
      map_add' := by
        intro x y
        apply Subtype.ext
        exact (hf (x+y) (.add (t x) (t y)) (by simp only [GroupTerm.eval,ht]; rfl)) }
    have hi : Function.Injective F := by
      intro x y h
      apply Subtype.ext
      have h' : (t x).eval b = (t y).eval b := congrArg Subtype.val h
      simpa only [ht] using (hab (t x) (t y)).mpr h'
    have hs : Function.Surjective F := by
      intro y
      obtain ⟨s,hs⟩ := closure_term_representation H n b (y:H) y.property
      let x : A := ⟨s.eval a,term_closure_membership G n a s⟩
      exact ⟨x,Subtype.ext ((hf x s rfl).trans hs)⟩
    refine ⟨AddEquiv.ofBijective F ⟨hi,hs⟩,?_⟩
    intro i
    exact hf ⟨a i,AddSubgroup.subset_closure ⟨i,rfl⟩⟩ (.var i) rfl
  · rintro ⟨e,he⟩
    let aA : Fin n → A := fun i => ⟨a i,AddSubgroup.subset_closure ⟨i,rfl⟩⟩
    have h₁ := embedding_atomic_agreement A G A.subtype Subtype.val_injective n aA
    have h₂ := embedding_atomic_agreement A H (B.subtype.comp e.toAddMonoidHom)
      (Subtype.val_injective.comp e.injective) n aA
    have hb : (fun i => (B.subtype.comp e.toAddMonoidHom) (aA i)) = b := funext he
    rw [hb] at h₂
    intro s t
    exact (h₁ s t).symm.trans (h₂ s t)
end LogicLineages.ModelsAlgebra.PGroups
