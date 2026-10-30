module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteStepTargets
public import Mathlib.GroupTheory.Index
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem finite_step_finite_ulm : Targets.groupFiniteStepFiniteUlm := by
  intro G _ p S hstep hulm
  letI : Finite (pStep p S) := hstep
  letI : Finite (UlmLayer p S) := hulm
  let d : successorSocleSubgroup p S → pStep p S := fun a => ⟨a.val.val,a.property.1⟩
  have hd : Function.Injective d := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pStep p S => (z : G)) h
  letI : Finite (successorSocleSubgroup p S) := Finite.of_injective d hd
  have hs : Finite (pSocle p S) :=
    (AddSubgroup.finite_iff_finite_and_finiteIndex (successorSocleSubgroup p S)).mpr
      ⟨inferInstance, AddSubgroup.finiteIndex_of_finite_quotient⟩
  letI : Finite (pSocle p S) := hs
  let f : S →+ G := (nsmulAddMonoidHom p).comp S.subtype
  let ik : f.ker → pSocle p S := fun a => ⟨a.val.val,⟨a.val.property,a.property⟩⟩
  have hik : Function.Injective ik := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pSocle p S => (z : G)) h
  have hk : Finite f.ker := Finite.of_injective ik hik
  have hrsub : f.range ≤ pStep p S := by
    rintro _ ⟨a,rfl⟩
    exact ⟨a.val,a.property,rfl⟩
  let ir : f.range → pStep p S := fun a => ⟨a.val,hrsub a.property⟩
  have hir : Function.Injective ir := by
    intro a b h
    exact Subtype.ext (congrArg (fun z : pStep p S => (z : G)) h)
  have hr : Finite f.range := Finite.of_injective ir hir
  exact f.finite_iff_finite_ker_range.mpr ⟨hk,hr⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
