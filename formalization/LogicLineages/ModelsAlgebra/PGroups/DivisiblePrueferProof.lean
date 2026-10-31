module
public import LogicLineages.ModelsAlgebra.PGroups.DivisiblePrueferTargets
public import LogicLineages.ModelsAlgebra.PGroups.PrueferDirectSumProof
public import LogicLineages.ModelsAlgebra.PGroups.PrueferSocleIsoProof
public import LogicLineages.ModelsAlgebra.PGroups.PrimarySocleControlProof
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleExtensionProof
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary Module

private theorem realize_pruefer_basis (p:ℕ) [Fact p.Prime] (D:Type) [AddCommGroup D]
    (hp:∀x:D,∃k:ℕ,p^k • x=0) (hd:GroupDivisible D) (I:Type)
    (b:Basis I (ZMod p) (pSocle p (⊤ : AddSubgroup D))) :
    Nonempty (PrueferDirectSum p I ≃+ D) := by
  classical
  obtain ⟨e⟩ := pruefer_socle_iso p
  obtain ⟨c,hc⟩ := pruefer_direct_sum_socle p I e
  let S := pSocle p (⊤ : AddSubgroup D)
  let T := pSocle p (⊤ : AddSubgroup (PrueferModel p))
  let v (i:I) : T →+ D := S.subtype.comp
    ((LinearMap.toSpanSingleton (ZMod p) S (b i)).toAddMonoidHom.comp e.symm.toAddMonoidHom)
  have hu : ∀ i:I, ∃ u:PrueferModel p →+ D, ∀ x:T, u (x:PrueferModel p)=v i x :=
    fun i => divisible_hom_extension (PrueferModel p) D hd T (v i)
  choose u hu using hu
  let F : PrueferDirectSum p I →+ D := Finsupp.liftAddHom u
  have huc (i:I) (a:ZMod p) : u i (e a:PrueferModel p) = ((a • b i:S):D) := by
    rw [hu]
    change ((e.symm (e a) • b i:S):D) = _
    rw [e.symm_apply_apply]
  have hsingle (i:I) (a:ZMod p) :
      (c.symm (Finsupp.single i a):PrueferDirectSum p I) = Finsupp.single i (e a:PrueferModel p) := by
    apply Finsupp.ext
    intro j
    have hh := hc (c.symm (Finsupp.single i a)) j
    rw [c.apply_symm_apply] at hh
    rw [←hh]
    by_cases h:j=i
    · subst j
      simp only [Finsupp.single_eq_same]
    · simp only [Finsupp.single_eq_of_ne h,e.map_zero,ZeroMemClass.coe_zero]
  have hcoh : ∀ a:I→₀ZMod p, F (c.symm a:PrueferDirectSum p I) = (b.repr.symm a:D) := by
    intro a
    induction a using Finsupp.induction_linear with
    | zero => simp only [map_zero,ZeroMemClass.coe_zero]
    | add a d ha hd =>
      rw [map_add]
      change F ((c.symm a:PrueferDirectSum p I)+(c.symm d:PrueferDirectSum p I)) = _
      rw [map_add,ha,hd,b.repr.symm.map_add]
      rfl
    | single i a =>
      rw [hsingle]
      change (Finsupp.liftAddHom u) (Finsupp.single i (e a:PrueferModel p)) = _
      rw [Finsupp.liftAddHom_apply_single,huc,b.repr_symm_single]
  have hinj : Function.Injective F := by
    apply primary_socle_injectivity p (PrueferDirectSum p I) D (pruefer_direct_sum_nature p I).2 F
    intro x y h
    have hx := hcoh (c x)
    have hy := hcoh (c y)
    rw [c.symm_apply_apply] at hx hy
    have hb : b.repr.symm (c x)=b.repr.symm (c y) := Subtype.ext (hx.symm.trans (h.trans hy))
    exact c.injective (b.repr.symm.injective hb)
  have hsur : Function.Surjective F := by
    apply primary_divisible_socle_surjectivity p D (PrueferDirectSum p I)
      (Fact.out : p.Prime).ne_zero hp (pruefer_direct_sum_nature p I).1 F
    intro x
    refine ⟨c.symm (b.repr x),?_⟩
    rw [hcoh,b.repr.symm_apply_apply]
  exact ⟨AddEquiv.ofBijective F ⟨hinj,hsur⟩⟩

theorem divisible_pruefer_decomposition : Targets.divisiblePrueferDecomposition := by
  intro p _ D _ hp hd
  let I := Basis.ofVectorSpaceIndex (ZMod p) (pSocle p (⊤ : AddSubgroup D))
  let b : Basis I (ZMod p) (pSocle p (⊤ : AddSubgroup D)) := Basis.ofVectorSpace _ _
  obtain ⟨e⟩ := realize_pruefer_basis p D hp hd I b
  exact ⟨I,⟨e.symm⟩,b.mk_eq_rank''⟩

private def socle_equiv {D E:Type} [AddCommGroup D] [AddCommGroup E]
    (p:ℕ) (e:D≃+E) : pSocle p (⊤:AddSubgroup D) ≃+ pSocle p (⊤:AddSubgroup E) where
  toFun x := ⟨e x,AddSubgroup.mem_top _,by
    change p • e (x:D)=0
    have hx:p • (x:D)=0:=x.property.2
    rw [←map_nsmul,hx,map_zero]⟩
  invFun x := ⟨e.symm x,AddSubgroup.mem_top _,by
    change p • e.symm (x:E)=0
    have hx:p • (x:E)=0:=x.property.2
    rw [←map_nsmul,hx,map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_add' x y := Subtype.ext (e.map_add x y)

theorem divisible_primary_classification : Targets.divisiblePrimaryClassification := by
  intro p _ D E _ _ hp hq hd he
  constructor
  · rintro ⟨e⟩
    let s := socle_equiv p e
    let l := LinearEquiv.ofBijective (s.toAddMonoidHom.toZModLinearMap p) s.bijective
    exact l.rank_eq
  · intro h
    obtain ⟨I,⟨d⟩,hi⟩ := divisible_pruefer_decomposition p D hp hd
    obtain ⟨J,⟨e⟩,hj⟩ := divisible_pruefer_decomposition p E hq he
    obtain ⟨k⟩ := Cardinal.eq.mp (hi.trans (h.trans hj.symm))
    exact ⟨(d.trans (Finsupp.domCongr k)).trans e.symm⟩
end LogicLineages.ModelsAlgebra.PGroups
