module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTermTableTargets
public import LogicLineages.ModelsAlgebra.PGroups.ImageInfinitude
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth
universe u w

theorem distinct_term_matrix : Targets.groupDistinctTermMatrix.{u} := by
  intro G _ n m t a
  unfold distinctTermMatrix
  simp only [finite_conjunction_realization G n m]
  constructor
  · intro h i j he
    by_contra hne
    have hd := h i j
    simp only [if_neg hne, QF.Realize] at hd
    exact hd he
  · intro h i j
    by_cases hij : i = j
    · simp [hij, QF.Realize]
    · simp only [if_neg hij, QF.Realize]
      exact fun he => hij (h he)

theorem finite_term_table : Targets.groupFiniteTermTable.{u,w} := by
  classical
  intro K _ _ G _ n t a
  let e := Fintype.equivFin K
  simp only [finiteTermTable, QF.Realize, distinct_term_matrix G n (Fintype.card K),
    finite_conjunction_realization G n (Fintype.card K), GroupTerm.eval]
  constructor
  · rintro ⟨hinj,hzero,hneg,hadd⟩
    let f : K →+ G :=
      { toFun := fun x => (t x).eval a
        map_zero' := hzero
        map_add' := by
          intro x y
          simpa only [e, Equiv.symm_apply_apply] using hadd (e x) (e y) }
    refine ⟨f, ?_, fun _ => rfl⟩
    intro x y hxy
    apply e.injective
    apply hinj
    change (t x).eval a = (t y).eval a at hxy
    simpa only [e, Equiv.symm_apply_apply] using hxy
  · rintro ⟨f,hf,hvalue⟩
    refine ⟨?_,?_,?_,?_⟩
    · intro i j hij
      apply e.symm.injective
      apply hf
      simpa only [hvalue, e] using hij
    · simpa only [hvalue] using f.map_zero
    · intro i
      simpa only [hvalue, e] using f.map_neg (e.symm i)
    · intro i j
      simpa only [hvalue, e] using f.map_add (e.symm i) (e.symm j)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
