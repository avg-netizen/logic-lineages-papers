module

public import LogicLineages.ModelsAlgebra.PGroups.CoordinateUlmTargets
public import LogicLineages.ModelsAlgebra.PGroups.CoordinateFiltration
public import Mathlib.Algebra.Module.Submodule.Equiv

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u v

theorem pi_finite_ulm : Targets.groupPiFiniteUlm.{u,v} := by
  classical
  intro ι G _ p j
  let S := pSocle p (finiteFiltration p j : AddSubgroup (∀ i, G i))
  let T (i : ι) := pSocle p (finiteFiltration p j : AddSubgroup (G i))
  let N (i : ι) := successorSocleSubgroup p (finiteFiltration p j : AddSubgroup (G i))
  let coord (x : S) (i : ι) : T i :=
    ⟨x.val i, (pi_finite_socle ι G p j x.val).mp x.property i⟩
  let f : S →+ (∀ i, UlmLayer p (finiteFiltration p j : AddSubgroup (G i))) :=
    { toFun := fun x i => QuotientAddGroup.mk' (N i) (coord x i)
      map_zero' := by funext i; rfl
      map_add' := by
        intro x y
        funext i
        exact map_add (QuotientAddGroup.mk' (N i)) (coord x i) (coord y i) }
  have hsurj : Function.Surjective f := by
    intro x
    have hx (i : ι) := QuotientAddGroup.mk'_surjective (N i) (x i)
    let y (i : ι) : T i := Classical.choose (hx i)
    let z : S := ⟨fun i => (y i).val,
      (pi_finite_socle ι G p j _).mpr fun i => (y i).property⟩
    refine ⟨z, ?_⟩
    funext i
    exact Classical.choose_spec (hx i)
  have hker : successorSocleSubgroup p (finiteFiltration p j : AddSubgroup (∀ i, G i)) = f.ker := by
    ext x
    change (x.val ∈ pSocle p (finiteFiltration p (j + 1))) ↔ f x = 0
    rw [pi_finite_socle]
    constructor
    · intro hx
      funext i
      exact (QuotientAddGroup.eq_zero_iff _).mpr (hx i)
    · intro hx i
      exact (QuotientAddGroup.eq_zero_iff (coord x i)).mp (congrArg (fun z => z i) hx)
  let e := QuotientAddGroup.liftEquiv _ hsurj hker
  exact ⟨LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) e.bijective⟩

theorem finsupp_finite_ulm : Targets.groupFinsuppFiniteUlm.{u,v} := by
  classical
  intro ι G _ p j
  let S := pSocle p (finiteFiltration p j : AddSubgroup (ι →₀ G))
  let T := pSocle p (finiteFiltration p j : AddSubgroup G)
  let N := successorSocleSubgroup p (finiteFiltration p j : AddSubgroup G)
  let Q := UlmLayer p (finiteFiltration p j : AddSubgroup G)
  let q : T →+ Q := QuotientAddGroup.mk' N
  let coord (x : S) (i : ι) : T :=
    ⟨x.val i, (finsupp_finite_socle ι G p j x.val).mp x.property i⟩
  have hsupp (x : S) (i : ι) : q (coord x i) ≠ 0 → i ∈ x.val.support := by
    intro hi
    apply Finsupp.mem_support_iff.mpr
    intro hz
    apply hi
    have hc : coord x i = 0 := Subtype.ext hz
    rw [hc, map_zero]
  let f : S →+ (ι →₀ Q) :=
    { toFun := fun x => Finsupp.onFinset x.val.support (fun i => q (coord x i)) (hsupp x)
      map_zero' := by apply Finsupp.ext; intro i; exact map_zero q
      map_add' := by
        intro x y
        apply Finsupp.ext
        intro i
        exact map_add q (coord x i) (coord y i) }
  have hsurj : Function.Surjective f := by
    intro x
    let rep : Q → T := fun a => if h0 : a = 0 then 0 else
      Classical.choose (QuotientAddGroup.mk'_surjective N a)
    have rep_zero : rep 0 = 0 := by simp [rep]
    have rep_spec (a : Q) : q (rep a) = a := by
      by_cases h0 : a = 0
      · simp [rep, h0]
      · simp only [rep, dif_neg h0]
        exact Classical.choose_spec (QuotientAddGroup.mk'_surjective N a)
    let y : ι →₀ G := x.mapRange (fun a => (rep a).val) (by rw [rep_zero]; rfl)
    let z : S := ⟨y, (finsupp_finite_socle ι G p j y).mpr fun i => (rep (x i)).property⟩
    refine ⟨z, ?_⟩
    apply Finsupp.ext
    intro i
    exact rep_spec (x i)
  have hker : successorSocleSubgroup p (finiteFiltration p j : AddSubgroup (ι →₀ G)) = f.ker := by
    ext x
    change (x.val ∈ pSocle p (finiteFiltration p (j + 1))) ↔ f x = 0
    rw [finsupp_finite_socle]
    constructor
    · intro hx
      apply Finsupp.ext
      intro i
      exact (QuotientAddGroup.eq_zero_iff _).mpr (hx i)
    · intro hx i
      exact (QuotientAddGroup.eq_zero_iff (coord x i)).mp (congrArg (fun z : ι →₀ Q => z i) hx)
  let e := QuotientAddGroup.liftEquiv _ hsurj hker
  exact ⟨LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) e.bijective⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
