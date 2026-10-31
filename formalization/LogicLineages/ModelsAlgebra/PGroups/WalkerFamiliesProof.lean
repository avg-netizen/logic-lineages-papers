module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerFamiliesTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerReservoirProof
public import Mathlib.Algebra.Group.Subgroup.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem filtration_prod (p : ℕ) (α : Ordinal.{0}) (G H : Type)
    [AddCommGroup G] [AddCommGroup H] :
    (transfiniteFiltration p α : AddSubgroup (G × H)) =
      (transfiniteFiltration p α : AddSubgroup G).prod (transfiniteFiltration p α : AddSubgroup H) := by
  refine Ordinal.limitRecOn α ?_ (fun β ih => ?_) (fun β hβ ih => ?_)
  · simp only [transfiniteFiltration_zero]
    ext x
    simp
  · rw [transfiniteFiltration_add_one, ih, transfiniteFiltration_add_one,
      transfiniteFiltration_add_one]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y.1, hy.1, rfl⟩, ⟨y.2, hy.2, rfl⟩⟩
    · rintro ⟨⟨a, ha, heqa⟩, ⟨b, hb, heqb⟩⟩
      exact ⟨(a,b), ⟨ha,hb⟩, Prod.ext heqa heqb⟩
  · rw [transfiniteFiltration_limit p hβ, transfiniteFiltration_limit p hβ,
      transfiniteFiltration_limit p hβ]
    ext x
    simp only [AddSubgroup.mem_iInf, AddSubgroup.mem_prod]
    constructor
    · intro hx
      exact ⟨fun γ => (ih γ.1 γ.2 ▸ hx γ).1, fun γ => (ih γ.1 γ.2 ▸ hx γ).2⟩
    · rintro ⟨hx,hy⟩ γ
      rw [ih γ.1 γ.2]
      exact ⟨hx γ, hy γ⟩

private noncomputable def prod_stage_equiv (p : ℕ) (α : Ordinal.{0}) (G H : Type)
    [AddCommGroup G] [AddCommGroup H] :
    (transfiniteFiltration p α : AddSubgroup (G × H)) ≃+
      (↥(transfiniteFiltration p α : AddSubgroup G) × ↥(transfiniteFiltration p α : AddSubgroup H)) :=
  (AddEquiv.addSubgroupCongr (filtration_prod p α G H)).trans (AddSubgroup.prodEquiv _ _)

private noncomputable def sum_stage_equiv (p : ℕ) (α : Ordinal.{0}) {ι : Type}
    (G : ι → Type) [∀ i, AddCommGroup (G i)] :
    (transfiniteFiltration p α : AddSubgroup (DirectSum ι G)) ≃+
      DirectSum ι (fun i => (transfiniteFiltration p α : AddSubgroup (G i))) :=
  (AddEquiv.addSubgroupCongr (transfinite_direct_sum p α)).trans
    (AddMonoidHom.ofInjective ((DirectSum.map_injective _).mpr
      (fun _ => Subtype.val_injective))).symm

private theorem sum_stage_zero (p : ℕ) (α : Ordinal.{0}) {ι : Type}
    (G : ι → Type) [∀ i, AddCommGroup (G i)]
    (h : ∀ i, (transfiniteFiltration p α : AddSubgroup (G i)) = ⊥) :
    (transfiniteFiltration p α : AddSubgroup (DirectSum ι G)) = ⊥ := by
  rw [transfinite_direct_sum]
  apply le_antisymm
  · intro x hx
    change x = 0
    apply DirectSum.ext
    intro i
    have hi := (direct_sum_subgroup_coordinates _ x).mp hx i
    rw [h i] at hi
    exact hi
  · exact bot_le

private theorem later_zero (p : ℕ) {α β : Ordinal.{0}} (G : Type) [AddCommGroup G]
    (hα : (transfiniteFiltration p α : AddSubgroup G) = ⊥) (h : α ≤ β) :
    (transfiniteFiltration p β : AddSubgroup G) = ⊥ :=
  le_antisymm ((transfiniteFiltration_antitone p h).trans hα.le) bot_le

theorem walker_source_families : Targets.walkerSourceFamilies := by
  classical
  intro p _ δ _ r
  letI : Countable (δ+1).ToType := walker_countable_successor δ
  letI : Countable (WalkerSourceGroup p δ) := (walker_source_group_nature p δ).1
  letI : Countable (WalkerSourceGroup p (δ+1)) := (walker_source_group_nature p (δ+1)).1
  letI : Countable (WalkerLowerReservoir p δ) := (walker_lower_reservoir p δ).1
  letI : Countable (DirectSum (Fin r) (fun _ => WalkerSourceGroup p δ)) :=
    inferInstanceAs (Countable (Π₀ _ : Fin r, WalkerSourceGroup p δ))
  letI : Countable (DirectSum ℕ (fun _ => WalkerSourceGroup p (δ+1))) :=
    inferInstanceAs (Countable (Π₀ _ : ℕ, WalkerSourceGroup p (δ+1)))
  obtain ⟨e⟩ := (walker_source_terminal p δ).1
  obtain ⟨e2⟩ := walker_source_double_terminal p δ
  let efin := (sum_stage_equiv p δ (fun _ : Fin r => WalkerSourceGroup p δ)).trans
    ((DFinsupp.mapRange.addEquiv (fun _ => e)).trans (DirectSum.addEquivProd (fun _ : Fin r => ZMod p)))
  let einf := (sum_stage_equiv p δ (fun _ : ℕ => WalkerSourceGroup p (δ+1))).trans
    (DFinsupp.mapRange.addEquiv (fun _ => e2))
  have hb := (walker_lower_reservoir p δ).2.2.1
  let eb := AddEquiv.addSubgroupCongr hb
  let eo := (prod_stage_equiv p δ (WalkerLowerReservoir p δ)
      (DirectSum (Fin r) (fun _ => WalkerSourceGroup p δ))).trans
    ((eb.prodCongr efin).trans (AddEquiv.uniqueProd))
  have ho : (transfiniteFiltration p (δ+1) : AddSubgroup (WalkerOdd p δ r)) = ⊥ := by
    rw [filtration_prod]
    rw [later_zero p (WalkerLowerReservoir p δ) hb (by exact le_self_add),
      sum_stage_zero p (δ+1) _ (fun _ => (walker_source_terminal p δ).2)]
    simp
  refine ⟨inferInstance, inferInstance, ⟨eo⟩, ?_, ho, ?_⟩
  · exact ⟨(prod_stage_equiv p δ (WalkerOdd p δ r)
      (DirectSum ℕ (fun _ => WalkerSourceGroup p (δ+1)))).trans (eo.prodCongr einf)⟩
  · rw [filtration_prod]
    rw [later_zero p (WalkerOdd p δ r) ho (by simpa only [add_assoc, one_add_one_eq_two] using (le_self_add : δ+1 ≤ (δ+1)+1))]
    have hi : (transfiniteFiltration p (δ+2) :
        AddSubgroup (DirectSum ℕ (fun _ => WalkerSourceGroup p (δ+1)))) = ⊥ := by
      apply sum_stage_zero
      intro _
      simpa only [add_assoc, one_add_one_eq_two] using (walker_source_terminal p (δ+1)).2
    rw [hi]
    simp
end LogicLineages.ModelsAlgebra.PGroups
