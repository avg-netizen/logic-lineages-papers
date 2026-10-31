module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedLengthTargets
public import LogicLineages.ModelsAlgebra.PGroups.CountableReducedZeroProof
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTail
public import LogicLineages.ModelsAlgebra.PGroups.FiniteOrdinalFiltration
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
private theorem countable_below {a b:Ordinal.{0}} (h:a≤b) (hb:Countable b.ToType) : Countable a.ToType := by
  letI := hb
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_toType]
  exact (Ordinal.card_le_card h).trans (by simpa only [Cardinal.mk_toType] using (Cardinal.mk_le_aleph0 (α:=b.ToType)))

theorem countable_reduced_exact_length : Targets.countableReducedExactLength := by
  intro G _ _ p _ hG hr
  obtain ⟨δ,hδ,_,hz⟩ := countable_reduced_zero_limit G p hG hr
  obtain ⟨ell,hell,hmin⟩ := wellFounded_lt.has_min
    {α:Ordinal.{0} | (transfiniteFiltration p α : AddSubgroup G)=⊥} ⟨δ,hz⟩
  have hle : ell≤δ := le_of_not_gt (hmin δ hz)
  refine ⟨ell,⟨countable_below hle hδ,hell,?_⟩,?_⟩
  · intro α hα ha
    exact hmin α ha hα
  · intro β hβ
    apply le_antisymm
    · by_contra hn
      exact hβ.2.2 ell (lt_of_not_ge hn) hell
    · exact le_of_not_gt (hmin β hβ.2.1)

theorem countable_length_normal_form : Targets.countableLengthNormalForm := by
  intro ell hc
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (Ordinal.mod_lt ell Ordinal.omega0_ne_zero)
  let γ := ell/Ordinal.omega0
  have hγ : γ≤ell := (Ordinal.le_mul_right γ Ordinal.omega0_pos).trans (Ordinal.mul_div_le ell Ordinal.omega0)
  have he : ell=Ordinal.omega0*γ+n := by rw [←hn]; exact (Ordinal.div_add_mod ell Ordinal.omega0).symm
  refine ⟨(γ,n),⟨countable_below hγ hc,he⟩,?_⟩
  rintro ⟨η,m⟩ ⟨_,hm⟩
  have hη : η=γ := by
    dsimp only [γ]
    rw [hm,Ordinal.mul_add_div _ Ordinal.omega0_ne_zero,
      Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 m),add_zero]
  have hmn : (m:Ordinal.{0})=(n:Ordinal.{0}) := by
    have hmod := congrArg (fun x:Ordinal.{0}=>x%Ordinal.omega0) (hm.symm.trans he)
    simpa only [Ordinal.mul_add_mod_self,Ordinal.mod_eq_of_lt (Ordinal.natCast_lt_omega0 m),
      Ordinal.mod_eq_of_lt (Ordinal.natCast_lt_omega0 n)] using hmod
  exact Prod.ext hη (by exact_mod_cast hmn)

theorem exact_length_terminal_bound : Targets.exactLengthTerminalBound := by
  intro G _ p γ n hlen
  let δ:Ordinal := Ordinal.omega0*γ
  let S:AddSubgroup G := transfiniteFiltration p δ
  have hz : (finiteFiltration p n : AddSubgroup S)=⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hm := (transfinite_tail_membership G p δ (n:Ordinal) x).mp
      (by rwa [finite_ordinal_filtration])
    rw [hlen.1,AddSubgroup.mem_bot] at hm
    exact Subtype.ext hm
  refine ⟨?_,?_⟩
  · intro x
    have hm : p^n • x ∈ (finiteFiltration p n : AddSubgroup S) := by
      rw [GroupInfinitary.finite_filtration_multiple_image]
      exact ⟨x,rfl⟩
    simpa only [hz,AddSubgroup.mem_bot] using hm
  · intro hn
    by_contra h
    push_neg at h
    have hz' : (finiteFiltration p (n-1) : AddSubgroup S)=⊥ := by
      rw [GroupInfinitary.finite_filtration_multiple_image]
      apply le_antisymm _ bot_le
      rintro x ⟨y,rfl⟩
      exact h y
    have hm := transfinite_tail_image G p δ ((n-1:ℕ):Ordinal)
    rw [finite_ordinal_filtration,hz',AddSubgroup.map_bot] at hm
    apply hlen.2 (δ+((n-1:ℕ):Ordinal)) _ hm.symm
    exact (add_lt_add_iff_left δ).mpr (by exact_mod_cast Nat.sub_lt hn (by decide:0<1))
end LogicLineages.ModelsAlgebra.PGroups
