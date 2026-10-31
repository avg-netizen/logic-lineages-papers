module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalDeletionOddTargets
public import LogicLineages.ModelsAlgebra.PGroups.TerminalFiniteLiftProof
public import LogicLineages.ModelsAlgebra.PGroups.LocalSocleBFProof
public import LogicLineages.ModelsAlgebra.PGroups.QuotientExactLength
public import LogicLineages.ModelsAlgebra.PGroups.TerminalLayer
public import LogicLineages.ModelsAlgebra.PGroups.ZeroStageReduced
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth

theorem terminal_deletion_odd : Targets.terminalDeletionOdd := by
  classical
  intro G _ _ p _ hG rG γ K T N hsplit hdis hN hbound hw
  letI : Countable (G ⧸ T) := (QuotientAddGroup.mk'_surjective T).countable
  let δ : Ordinal := Ordinal.omega0*γ
  let q := QuotientAddGroup.mk' T
  have hT : T ≤ (transfiniteFiltration p δ : AddSubgroup G) := by
    rw [hsplit]; exact le_sup_right
  have hRank : UlmRanksAgreeBelow p G (G ⧸ T) δ :=
    fun α hα => ((full_quotient_filtration p T γ hT).2 α hα).2
  have hlen := quotient_exact_length G p δ K T N hsplit hdis hN hbound hw
  have rQ : IsReducedAddGroup (G ⧸ T) :=
    zero_stage_reduced (G ⧸ T) p (Fact.out : p.Prime).ne_zero (δ+N) hlen.1.2
  have hQ := p_primary_quotient G p T hG
  have lG : StagesNonzeroBelow p G δ := fun α hα => (hlen.2 α (hα.trans_le le_self_add)).1
  have lQ : StagesNonzeroBelow p (G ⧸ T) δ := fun α hα => (hlen.2 α (hα.trans_le le_self_add)).2
  refine ⟨hRank,terminal_layer_quotient G p δ K T hsplit hdis,rQ,hlen.1,hlen.2,?_⟩
  intro n a hA
  apply (back_forth_successor (2*γ) G (G ⧸ T) n a (fun i => q (a i))).mpr
  intro m d
  let A := AddSubgroup.closure (Set.range a)
  let b : Fin n → G ⧸ T := fun i => q (a i)
  let D := AddSubgroup.closure (Set.range (append b d))
  letI : Finite D := p_primary_finite_tuple_closure (G ⧸ T) p
    (Fact.out : p.Prime).ne_zero hQ (n+m) (append b d)
  have ha (i) : a i ∈ A := AddSubgroup.subset_closure ⟨i,rfl⟩
  have hb (i) : b i ∈ D := AddSubgroup.subset_closure
    ⟨Fin.castAdd m i,by simp [append]⟩
  have hd (i) : d i ∈ D := AddSubgroup.subset_closure
    ⟨Fin.natAdd n i,by simp [append]⟩
  have hAD : A.map q ≤ D := by
    apply (AddSubgroup.map_le_iff_le_comap).mpr
    apply (AddSubgroup.closure_le (D.comap q)).mpr
    rintro x ⟨i,rfl⟩
    exact hb i
  obtain ⟨F,hF,hFa,hFp⟩ := terminal_finite_lift G p hG γ A K T hsplit hdis hA D hAD
  let e : D ≃+ F.range := AddMonoidHom.ofInjective hF
  have hpres : MapCutsExact p e.symm δ := by
    intro c β hβ
    have hv : F (e.symm c) = (c:G) := congrArg Subtype.val (e.apply_symm_apply c)
    have hh := hFp (e.symm c) β hβ
    rw [hv] at hh
    exact hh.symm
  letI : Finite F.range := Finite.of_surjective e e.surjective
  have hr := reduced_limit_cut_comparison G (G ⧸ T) p hG hQ rG rQ F.range D e.symm γ lG lQ hRank hpres
  let s : Fin (n+m) → D := append (fun i => ⟨b i,hb i⟩) (fun i => ⟨d i,hd i⟩)
  let t : Fin (n+m) → F.range := fun i => e (s i)
  let c : Fin m → G := fun i => F ⟨d i,hd i⟩
  have hl : (fun i => (e.symm (t i):G ⧸ T)) = append b d := by
    funext i
    dsimp only [t]
    rw [AddEquiv.symm_apply_apply]
    induction i using Fin.addCases <;> simp [s,append]
  have haF (i) : F ⟨b i,hb i⟩ = a i := hFa ⟨a i,ha i⟩
  have hh : (fun i => (t i:G)) = append a c := by
    funext i
    change F (s i) = _
    induction i using Fin.addCases <;> simp [s,c,append,haF]
  have h := hr (n+m) t
  change BackAndForth (2*γ) (fun i => (e.symm (t i):G ⧸ T)) (fun i => (t i:G)) at h
  rw [hl,hh] at h
  exact ⟨c,h⟩
end LogicLineages.ModelsAlgebra.PGroups
