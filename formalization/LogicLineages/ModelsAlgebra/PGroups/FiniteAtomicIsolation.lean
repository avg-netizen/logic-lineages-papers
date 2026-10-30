module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteAtomicIsolationTargets
public import LogicLineages.ModelsAlgebra.PGroups.TermClosure
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTermTable
public import LogicLineages.ModelsAlgebra.PGroups.Infinitary
public import LogicLineages.ModelsAlgebra.PGroups.BackForthCore
public import LogicLineages.ModelsAlgebra.PGroups.TorsionScott
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth
universe u

theorem finite_atomic_isolation : Targets.groupFiniteAtomicIsolation.{u} := by
  classical
  intro G _ n a hfinite
  let S := AddSubgroup.closure (Set.range a)
  letI : Finite S := hfinite
  letI : Fintype S := Fintype.ofFinite S
  choose t ht using fun x : S => closure_term_representation G n a (x:G) x.property
  let aS : Fin n → S := fun j => ⟨a j,AddSubgroup.subset_closure ⟨j,rfl⟩⟩
  let q : QF n := .and (finiteTermTable S t)
    (finiteAnd n fun j => .equal (.var j) (t (aS j)))
  have hqa : q.Realize a := by
    constructor
    · exact (finite_term_table S G n t a).mpr ⟨S.subtype,Subtype.val_injective,fun x => (ht x).symm⟩
    · apply (finite_conjunction_realization G n n _ a).mpr
      intro j
      exact (ht (aS j)).symm
  refine ⟨q,hqa,?_⟩
  intro H _ b
  constructor
  · rintro ⟨hTable,hVars⟩
    obtain ⟨f,hf,hvalue⟩ := (finite_term_table S H n t b).mp hTable
    have hb (j) : f (aS j) = b j := by
      have hv : b j = (t (aS j)).eval b :=
        (finite_conjunction_realization H n n _ b).mp hVars j
      exact (hvalue (aS j)).trans hv.symm
    have hleft := embedding_atomic_agreement S G S.subtype Subtype.val_injective n aS
    have hright := embedding_atomic_agreement S H f hf n aS
    have he : (fun j => f (aS j)) = b := funext hb
    rw [he] at hright
    intro s t
    exact (hleft s t).symm.trans (hright s t)
  · intro hab
    exact (qf_truth_agreement G H n a b hab q).mp hqa

theorem p_primary_atomic_isolation : Targets.groupPPrimaryAtomicIsolation.{u} := by
  intro p hp G _ hG n a
  have hLF := torsion_locally_finite G (p_primary_torsion p hp G hG)
  letI : Fintype (AddSubgroup.closure (Set.range a)) := (hLF n a).fintype
  exact finite_atomic_isolation G n a inferInstance

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
