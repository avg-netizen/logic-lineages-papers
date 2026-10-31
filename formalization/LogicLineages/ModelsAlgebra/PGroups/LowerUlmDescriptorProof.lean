module
public import LogicLineages.ModelsAlgebra.PGroups.LowerUlmDescriptorTargets
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteUlmSyntaxProof
public import LogicLineages.ModelsAlgebra.PGroups.CountablePiAssemblyProof
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryWrap
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary

private theorem countable_below (γ : Ordinal) [Countable γ.ToType]
    (β : Ordinal) (h : β ≤ γ) : Countable β.ToType := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_toType]
  exact (Ordinal.card_le_card h).trans (by
    simpa only [Cardinal.mk_toType] using (Cardinal.mk_le_aleph0 (α := γ.ToType)))

private theorem single_lower_descriptor (p : ℕ) [Fact p.Prime] (G : Type)
    [AddCommGroup G] [Countable G] (γ η : Ordinal.{0}) [Countable η.ToType]
    (hηγ : η<γ) (j : ℕ) :
    ∃ φ : Formula 0, Complexity .pi (2*γ+1) φ ∧
      ∀ (H : Type) [AddCommGroup H] [Countable H], φ.Realize (Fin.elim0 : Fin 0 → H) ↔
        Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (Ordinal.omega0*η+j) : AddSubgroup G)) =
        Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (Ordinal.omega0*η+j) : AddSubgroup H)) := by
  classical
  let κ := Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (Ordinal.omega0*η+j) : AddSubgroup G))
  have hκ : κ ≤ Cardinal.aleph0 := countable_transfinite_ulm_bound p G _
  have hlevel : 2*η+2 ≤ 2*γ := by
    simpa only [mul_add_one] using
      (Ordinal.isNormal_mul_right (by norm_num : (0:Ordinal)<2)).monotone (Order.add_one_le_iff.mpr hηγ)
  have hstrict : 2*η+2 < 2*γ+1 := hlevel.trans_lt (Order.lt_succ _)
  have hpos : 2*γ+1 ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le (Order.lt_succ _))
  have hrpos : 2*η+2 ≠ 0 := by
    simpa only [Order.succ_eq_add_one,add_assoc,one_add_one_eq_two] using
      (ne_of_gt (lt_of_le_of_lt zero_le (Order.lt_succ (2*η+1))))
  by_cases hk : κ < Cardinal.aleph0
  · let m := κ.toNat
    have hm : (m:Cardinal)=κ := Cardinal.cast_toNat_of_lt_aleph0 hk
    obtain ⟨d,hd,hsem⟩ := transfinite_ulm_exact_definable p η j m
    let φ := piConjunction (piWrap d.sigmaPart) d.piPart
    refine ⟨φ,pi_conjunction_complexity _ hpos 0 _ _
      (pi_wrap_complexity _ _ hpos hstrict 0 _ hd.1)
      (positive_complexity_monotone .pi _ _ 0 _ hrpos hstrict.le hd.2),?_⟩
    intro H _ _
    have ht : φ.Realize (Fin.elim0 : Fin 0 → H) ↔ d.Realize Fin.elim0 :=
      (pi_conjunction_realization H 0 _ _ _).trans
        (and_congr (pi_wrap_realization H 0 _ _) Iff.rfl)
    rw [ht,hsem H]
    change (_ = (m:Cardinal)) ↔ κ = _
    rw [← hm]
    exact eq_comm
  · have he : κ=Cardinal.aleph0 := le_antisymm hκ (le_of_not_gt hk)
    obtain ⟨φ,hφ,hsem⟩ := transfinite_ulm_infinite_definable p η j
    have hstep : (2*η+2)+1 = 2*η+3 := by rw [add_assoc]; congr 1
    have hbound : 2*η+3 ≤ 2*γ+1 := by
      rw [← hstep]
      exact add_le_add hlevel le_rfl
    have hpos' : 2*η+3 ≠ 0 := by
      rw [← hstep]
      exact ne_of_gt (lt_of_le_of_lt zero_le (Order.lt_succ _))
    refine ⟨φ,positive_complexity_monotone .pi _ _ 0 φ hpos' hbound hφ,?_⟩
    intro H _ _
    rw [hsem H]
    change Cardinal.aleph0 ≤ _ ↔ κ = _
    rw [he]
    constructor
    · intro h
      exact (le_antisymm (countable_transfinite_ulm_bound p H _) h).symm
    · intro h; exact h.le

theorem lower_ulm_descriptor : Targets.lowerUlmDescriptor := by
  classical
  intro p _ G _ _ γ _
  let I := γ.ToType × ℕ
  let η (i : I) : Ordinal := Ordinal.typein (α := γ.ToType) (· < ·) i.1
  have hη (i : I) : η i < γ := Ordinal.typein_lt_self i.1
  have hex (i : I) : ∃ φ : Formula 0, Complexity .pi (2*γ+1) φ ∧
      ∀ (H : Type) [AddCommGroup H] [Countable H], φ.Realize (Fin.elim0 : Fin 0 → H) ↔
        Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (Ordinal.omega0*η i+i.2) : AddSubgroup G)) =
        Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (Ordinal.omega0*η i+i.2) : AddSubgroup H)) := by
    letI := countable_below γ (η i) (hη i).le
    exact single_lower_descriptor p G γ (η i) (hη i) i.2
  choose φ hφ hsem using hex
  obtain ⟨ψ,hψ,hψsem⟩ := countable_pi_assembly.{0} (2*γ+1)
    (ne_of_gt (lt_of_le_of_lt zero_le (Order.lt_succ _))) I 0 φ hφ
  refine ⟨ψ,hψ,?_⟩
  intro H _ _
  rw [hψsem H Fin.elim0]
  constructor
  · intro h α hα
    have hdiv : α/Ordinal.omega0 < γ := (Ordinal.lt_mul_iff_div_lt Ordinal.omega0_ne_zero).mp hα
    obtain ⟨i,hi⟩ := Ordinal.typein_surj (α := γ.ToType) (· < ·) (by simpa using hdiv)
    obtain ⟨j,hj⟩ := Ordinal.lt_omega0.mp (Ordinal.mod_lt α Ordinal.omega0_ne_zero)
    have he : Ordinal.omega0*η (i,j)+j = α := by
      change Ordinal.omega0*Ordinal.typein (α := γ.ToType) (· < ·) i+j = α
      rw [hi,← hj]
      exact Ordinal.div_add_mod α Ordinal.omega0
    have hh := (hsem (i,j) H).mp (h (i,j))
    change Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (Ordinal.omega0*η (i,j)+j) : AddSubgroup G)) =
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (Ordinal.omega0*η (i,j)+j) : AddSubgroup H)) at hh
    rw [he] at hh
    exact hh
  · intro h i
    apply (hsem i H).mpr
    apply h
    calc
      Ordinal.omega0*η i+i.2 < Ordinal.omega0*η i+Ordinal.omega0 :=
        (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 i.2)
      _ = Ordinal.omega0*(η i+1) := (mul_add_one _ _).symm
      _ ≤ Ordinal.omega0*γ :=
        (Ordinal.isNormal_mul_right Ordinal.omega0_pos).monotone (Order.add_one_le_iff.mpr (hη i))
end LogicLineages.ModelsAlgebra.PGroups
