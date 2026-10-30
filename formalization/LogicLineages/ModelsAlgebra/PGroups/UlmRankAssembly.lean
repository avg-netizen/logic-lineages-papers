module

public import LogicLineages.ModelsAlgebra.PGroups.UlmRankAssemblyTargets
public import LogicLineages.ModelsAlgebra.PGroups.CoordinateUlm
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Field.ZMod

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u

private theorem prod_filtration (G H : Type u) [AddCommGroup G] [AddCommGroup H]
    (p j : ℕ) (x : G × H) : x ∈ finiteFiltration p j ↔
      x.1 ∈ finiteFiltration p j ∧ x.2 ∈ finiteFiltration p j := by
  rw [finite_filtration_multiple_image, finite_filtration_multiple_image,
    finite_filtration_multiple_image]
  change (∃ y : G × H, p ^ j • y = x) ↔
    (∃ a : G, p ^ j • a = x.1) ∧ (∃ b : H, p ^ j • b = x.2)
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.1, rfl⟩, ⟨y.2, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨(a,b), Prod.ext ha hb⟩

private theorem prod_socle (G H : Type u) [AddCommGroup G] [AddCommGroup H]
    (p j : ℕ) (x : G × H) : x ∈ pSocle p (finiteFiltration p j) ↔
      x.1 ∈ pSocle p (finiteFiltration p j) ∧ x.2 ∈ pSocle p (finiteFiltration p j) := by
  change (x ∈ finiteFiltration p j ∧ p • x = 0) ↔
    (x.1 ∈ finiteFiltration p j ∧ p • x.1 = 0) ∧
    (x.2 ∈ finiteFiltration p j ∧ p • x.2 = 0)
  rw [prod_filtration]
  constructor
  · rintro ⟨hx,hz⟩
    exact ⟨⟨hx.1, congrArg Prod.fst hz⟩, ⟨hx.2, congrArg Prod.snd hz⟩⟩
  · rintro ⟨ha,hb⟩
    exact ⟨⟨ha.1,hb.1⟩, Prod.ext ha.2 hb.2⟩

theorem product_finite_ulm : Targets.groupProductFiniteUlm.{u} := by
  classical
  intro G H _ _ p j
  let S := pSocle p (finiteFiltration p j : AddSubgroup (G × H))
  let NG := successorSocleSubgroup p (finiteFiltration p j : AddSubgroup G)
  let NH := successorSocleSubgroup p (finiteFiltration p j : AddSubgroup H)
  let a (x : S) : pSocle p (finiteFiltration p j : AddSubgroup G) :=
    ⟨x.val.1, ((prod_socle G H p j x.val).mp x.property).1⟩
  let b (x : S) : pSocle p (finiteFiltration p j : AddSubgroup H) :=
    ⟨x.val.2, ((prod_socle G H p j x.val).mp x.property).2⟩
  let f : S →+ (UlmLayer p (finiteFiltration p j : AddSubgroup G) ×
      UlmLayer p (finiteFiltration p j : AddSubgroup H)) :=
    { toFun := fun x => (QuotientAddGroup.mk' NG (a x), QuotientAddGroup.mk' NH (b x))
      map_zero' := rfl
      map_add' := fun x y => Prod.ext (map_add (QuotientAddGroup.mk' NG) (a x) (a y))
        (map_add (QuotientAddGroup.mk' NH) (b x) (b y)) }
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨y,hy⟩ := QuotientAddGroup.mk'_surjective NG x.1
    obtain ⟨z,hz⟩ := QuotientAddGroup.mk'_surjective NH x.2
    exact ⟨⟨(y.val,z.val), (prod_socle G H p j _).mpr ⟨y.property,z.property⟩⟩,
      Prod.ext hy hz⟩
  have hker : successorSocleSubgroup p (finiteFiltration p j : AddSubgroup (G × H)) = f.ker := by
    ext x
    change x.val ∈ pSocle p (finiteFiltration p (j+1)) ↔ f x = 0
    rw [prod_socle]
    constructor
    · rintro ⟨hx,hy⟩
      exact Prod.ext ((QuotientAddGroup.eq_zero_iff (a x)).mpr hx)
        ((QuotientAddGroup.eq_zero_iff (b x)).mpr hy)
    · intro hx
      exact ⟨(QuotientAddGroup.eq_zero_iff (a x)).mp (congrArg Prod.fst hx),
        (QuotientAddGroup.eq_zero_iff (b x)).mp (congrArg Prod.snd hx)⟩
  let e := QuotientAddGroup.liftEquiv _ hsurj hker
  exact ⟨LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) e.bijective⟩

theorem product_ulm_rank : Targets.groupProductUlmRank.{u} := by
  intro p _ G H _ _ j
  obtain ⟨e⟩ := product_finite_ulm G H p j
  rw [e.rank_eq]
  letI : Module.Free (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) :=
    Module.Free.of_divisionRing (ZMod p) _
  letI : Module.Free (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup H)) :=
    Module.Free.of_divisionRing (ZMod p) _
  exact rank_prod'

theorem pi_ulm_rank : Targets.groupPiUlmRank.{u} := by
  intro p _ ι _ G _ j
  obtain ⟨e⟩ := pi_finite_ulm ι G p j
  rw [e.rank_eq]
  letI : ∀ i, Module.Free (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup (G i))) :=
    fun i => Module.Free.of_divisionRing (ZMod p) _
  exact rank_pi

theorem finsupp_ulm_rank : Targets.groupFinsuppUlmRank.{u} := by
  intro p _ ι G _ j
  obtain ⟨e⟩ := finsupp_finite_ulm ι G p j
  rw [e.rank_eq]
  letI : Module.Free (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) :=
    Module.Free.of_divisionRing (ZMod p) _
  exact rank_finsupp' (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) ι

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
