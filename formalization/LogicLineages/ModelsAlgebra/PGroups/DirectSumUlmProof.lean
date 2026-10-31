module
public import LogicLineages.ModelsAlgebra.PGroups.DirectSumUlmTargets
public import LogicLineages.ModelsAlgebra.PGroups.DirectSumFiltrationProof
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v w

private theorem sum_socle_coordinates {ι : Type u} {G : ι → Type v}
    [∀ i, AddCommGroup (G i)] (p : ℕ) (α : Ordinal.{w}) (x : DirectSum ι G) :
    x ∈ pSocle p (transfiniteFiltration p α) ↔
      ∀ i, x i ∈ pSocle p (transfiniteFiltration p α : AddSubgroup (G i)) := by
  change (x ∈ transfiniteFiltration p α ∧ p • x = 0) ↔
    ∀ i, x i ∈ transfiniteFiltration p α ∧ p • x i = 0
  rw [transfinite_direct_sum, direct_sum_subgroup_coordinates]
  constructor
  · rintro ⟨hx,hz⟩ i
    exact ⟨hx i, congrArg (fun z : DirectSum ι G => z i) hz⟩
  · intro h
    refine ⟨fun i => (h i).1, ?_⟩
    apply DirectSum.ext
    exact fun i => (h i).2

theorem transfinite_direct_sum_ulm : Targets.transfiniteDirectSumUlm.{u,v,w} := by
  classical
  intro ι G _ p α
  let S := pSocle p (transfiniteFiltration p α : AddSubgroup (DirectSum ι G))
  let T (i : ι) := pSocle p (transfiniteFiltration p α : AddSubgroup (G i))
  let N (i : ι) := successorSocleSubgroup p (transfiniteFiltration p α : AddSubgroup (G i))
  let Q (i : ι) := UlmLayer p (transfiniteFiltration p α : AddSubgroup (G i))
  let q (i : ι) : T i →+ Q i := QuotientAddGroup.mk' (N i)
  let coord (x : S) (i : ι) : T i :=
    ⟨x.val i, (sum_socle_coordinates p α x.val).mp x.property i⟩
  let cf (x : S) : DirectSum ι (fun i => T i) :=
    DFinsupp.mk (DFinsupp.support x.val) (fun i => coord x i)
  have hc (x : S) (i : ι) : cf x i = coord x i := by
    dsimp only [cf]
    by_cases hi : i ∈ DFinsupp.support x.val
    · simp [DFinsupp.mk_apply, hi]
    · have hz : x.val i = 0 := DFinsupp.notMem_support_iff.mp hi
      simp only [DFinsupp.mk_apply, dif_neg hi]
      exact Subtype.ext hz.symm
  let c : S →+ DirectSum ι (fun i => T i) :=
    { toFun := cf
      map_zero' := by
        apply DirectSum.ext
        intro i
        rw [hc]
        rfl
      map_add' := by
        intro x y
        apply DirectSum.ext
        intro i
        rw [DirectSum.add_apply, hc, hc, hc]
        rfl }
  let f : S →+ DirectSum ι Q := (DirectSum.map q).comp c
  have hf (x : S) (i : ι) : f x i = q i (coord x i) := by
    change (DirectSum.map q) (cf x) i = _
    rw [DirectSum.map_apply, hc]
  have hsurj : Function.Surjective f := by
    intro x
    let rep (i : ι) : Q i → T i := fun a => if h0 : a = 0 then 0 else
      Classical.choose (QuotientAddGroup.mk'_surjective (N i) a)
    have rep_zero (i : ι) : rep i 0 = 0 := by simp [rep]
    have rep_spec (i : ι) (a : Q i) : q i (rep i a) = a := by
      by_cases h0 : a = 0
      · simp [rep, h0]
      · simp only [rep, dif_neg h0]
        exact Classical.choose_spec (QuotientAddGroup.mk'_surjective (N i) a)
    let y : DirectSum ι G := DFinsupp.mapRange (fun i a => (rep i a).val)
      (fun i => by rw [rep_zero]; rfl) x
    let z : S := ⟨y, (sum_socle_coordinates p α y).mpr (fun i => (rep i (x i)).property)⟩
    refine ⟨z, ?_⟩
    apply DirectSum.ext
    intro i
    rw [hf]
    exact rep_spec i (x i)
  have hker : successorSocleSubgroup p (transfiniteFiltration p α : AddSubgroup (DirectSum ι G)) = f.ker := by
    ext x
    change (x.val ∈ pSocle p (pStep p (transfiniteFiltration p α))) ↔ f x = 0
    rw [← transfiniteFiltration_add_one, sum_socle_coordinates]
    constructor
    · intro hx
      apply DirectSum.ext
      intro i
      rw [hf]
      apply (QuotientAddGroup.eq_zero_iff _).mpr
      change x.val i ∈ pSocle p (pStep p (transfiniteFiltration p α))
      rw [← transfiniteFiltration_add_one]
      exact hx i
    · intro hx i
      have hi : q i (coord x i) = 0 := by
        rw [← hf]
        exact congrArg (fun z : DirectSum ι Q => z i) hx
      have hn := (QuotientAddGroup.eq_zero_iff (coord x i)).mp hi
      change x.val i ∈ pSocle p (pStep p (transfiniteFiltration p α)) at hn
      rw [← transfiniteFiltration_add_one] at hn
      exact hn
  let e := QuotientAddGroup.liftEquiv _ hsurj hker
  exact ⟨LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) e.bijective⟩

theorem transfinite_direct_sum_ulm_rank : Targets.transfiniteDirectSumUlmRank.{u,v,w} := by
  intro ι G _ p _ α
  obtain ⟨e⟩ := transfinite_direct_sum_ulm (G := G) p α
  rw [e.rank_eq, rank_directSum]
end LogicLineages.ModelsAlgebra.PGroups
