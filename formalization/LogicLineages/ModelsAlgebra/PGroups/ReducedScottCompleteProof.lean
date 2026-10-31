module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedScottCompleteTargets
public import LogicLineages.ModelsAlgebra.PGroups.ReducedLengthProof
public import LogicLineages.ModelsAlgebra.PGroups.TerminalMultiplicityProof
public import LogicLineages.ModelsAlgebra.PGroups.RawTrivialExactProof
public import LogicLineages.ModelsAlgebra.PGroups.ZeroCutScottProof
public import LogicLineages.ModelsAlgebra.PGroups.ReducedOddSigmaProof
public import LogicLineages.ModelsAlgebra.PGroups.ReducedLimitDifferenceProof
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTailScottProof
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTailLowerProof
public import LogicLineages.ModelsAlgebra.PGroups.RawFiniteLower
public import LogicLineages.ModelsAlgebra.PGroups.OneInfiniteTailProof
public import LogicLineages.ModelsAlgebra.PGroups.OneInfiniteTailLowerProof
public import LogicLineages.ModelsAlgebra.PGroups.InfiniteTerminalSigmaProof
public import LogicLineages.ModelsAlgebra.PGroups.TwoInfiniteTailSigmaProof
public import LogicLineages.ModelsAlgebra.PGroups.TwoInfiniteTailLowerProof
public import LogicLineages.ModelsAlgebra.PGroups.BoundedTailScottProof
public import LogicLineages.ModelsAlgebra.PGroups.BoundedInfiniteRank
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary
private theorem infinite_of_rank (p:ℕ) [Fact p.Prime] (H:Type) [AddCommGroup H] (j:ℕ)
    (hj:TerminalRank p H j=Cardinal.aleph0) : Infinite H := by
  letI := infinite_ulm_infinite_filtration p H j hj
  exact Infinite.of_injective (fun x:(finiteFiltration p j:AddSubgroup H)=>(x:H)) Subtype.val_injective

private theorem terminal_patterns (p:ℕ) [Fact p.Prime] (H:Type) [AddCommGroup H] [Countable H]
    (N:ℕ) (hN:∀x:H,p^N • x=0) :
    Finite H ∨ (∃k:ℕ,OneInfiniteTerminal p H N k) ∨ TwoInfiniteTerminal p H N := by
  classical
  by_cases hf:Finite H
  · exact Or.inl hf
  letI : Infinite H := not_finite_iff_infinite.mp hf
  by_cases ht:TwoInfiniteTerminal p H N
  · exact Or.inr (Or.inr ht)
  obtain ⟨a,ha⟩ := bounded_infinite_rank_exists p H N hN
  refine Or.inr (Or.inl ⟨a.val+1,Nat.succ_pos _,Nat.succ_le_of_lt a.isLt,?_,?_⟩)
  · change TerminalRank p H (a.val+1-1)=Cardinal.aleph0
    rw [show a.val+1-1=a.val from by omega]
    exact ha
  · intro j hj hja
    apply lt_of_le_of_ne (countable_ulm_rank_bound p H j)
    intro he
    have hne : (⟨j,hj⟩:Fin N)≠a := by
      intro h
      exact hja (by simpa only [Nat.add_sub_cancel] using congrArg Fin.val h)
    rcases lt_or_gt_of_ne hne with hlt|hgt
    · exact ht ⟨⟨j,hj⟩,a,hlt,he,ha⟩
    · exact ht ⟨a,⟨j,hj⟩,hgt,ha,he⟩

theorem reduced_scott_full_source : Targets.reducedScottFullSource := by
  classical
  refine ⟨?_,raw_trivial_exact⟩
  intro G _ _ _ p _ hG hr
  obtain ⟨ell,hell,huniq⟩ := countable_reduced_exact_length G p hG hr
  obtain ⟨z,hz,hzuniq⟩ := countable_length_normal_form ell hell.1
  refine ⟨?_,?_⟩
  · refine ⟨z,⟨hz.1,?_⟩,?_⟩
    · rw [←hz.2]; exact hell.2
    · intro w hw
      have he : Ordinal.omega0*w.1+w.2=ell := by
        apply le_antisymm
        · by_contra hn
          exact hw.2.2 ell (lt_of_not_ge hn) hell.2.1
        · by_contra hn
          exact hell.2.2 _ (lt_of_not_ge hn) hw.2.1
      exact hzuniq w ⟨hw.1,he.symm⟩
  intro γ _ N hlen
  have hl : StagesNonzeroBelow p G (Ordinal.omega0*γ) :=
    fun α hα=>hlen.2 α (hα.trans_le le_self_add)
  have hb := exact_length_terminal_bound G p γ N hlen
  refine ⟨?_,?_⟩
  · intro hN
    subst N
    have hγ : 0<γ := by
      apply lt_of_le_of_ne zero_le
      intro hz
      have hz' : γ=0 := hz.symm
      have he : (⊤:AddSubgroup G)=⊥ := by
        simpa only [hz',mul_zero,Nat.cast_zero,add_zero,transfiniteFiltration_zero] using hlen.1
      obtain ⟨x,hx⟩ := exists_ne (0:G)
      have hx' : x∈(⊤:AddSubgroup G) := AddSubgroup.mem_top x
      rw [he,AddSubgroup.mem_bot] at hx'
      exact hx hx'
    have hzero : (transfiniteFiltration p (Ordinal.omega0*γ):AddSubgroup G)=⊥ := by
      simpa only [Nat.cast_zero,add_zero] using hlen.1
    exact ⟨hγ,⟨zero_cut_scott_upper p G γ hG hzero,
      reduced_odd_no_raw_sigma G p hG hr γ hγ hl⟩,
      reduced_limit_no_raw_difference G p hG hr γ hγ hl⟩
  · intro hN
    let H := (transfiniteFiltration p (Ordinal.omega0*γ):AddSubgroup G)
    have hlt : (0:Ordinal.{0})<(N:Ordinal.{0}) := by exact_mod_cast hN
    have hnz : H≠⊥ := hlen.2 _ (by
      simpa only [add_zero] using (add_lt_add_iff_left (Ordinal.omega0*γ)).mpr hlt)
    refine ⟨terminal_multiplicity_data p H N hN hb.1 (hb.2 hN),
      terminal_patterns p H N hb.1,?_,?_,?_⟩
    · intro hf
      letI : Finite H := hf
      refine ⟨finite_tail_scott_upper p G γ hG hf,?_,?_⟩
      · by_cases hz:γ=0
        · subst γ
          letI : Finite G := Finite.of_injective (fun x:G=>(⟨x,by simp [H,transfiniteFiltration_zero]⟩:H))
            (by intro x y h; exact congrArg Subtype.val h)
          simpa only [mul_zero,zero_add] using raw_finite_no_sigma_one_scott G
        · exact reduced_odd_no_raw_sigma G p hG hr γ (lt_of_le_of_ne zero_le (Ne.symm hz)) hl
      · by_cases hz:γ=0
        · subst γ
          simpa only [mul_zero,zero_add] using raw_nontrivial_no_pi_one_scott G
        · exact finite_tail_no_pi G p hG hr γ (lt_of_le_of_ne zero_le (Ne.symm hz)) hf hnz
    · intro k hk
      have hinf : Infinite H := infinite_of_rank p H (k-1) hk.2.2.1
      have hSigma := infinite_terminal_no_raw_sigma G p hG hr γ N hb.1 hinf
      refine ⟨?_,?_⟩
      · intro hshort
        exact ⟨one_infinite_tail_pi_upper p G γ k N hG hk.1 hk.2.1 hb.1 hk.2.2.1 hk.2.2.2 hshort,hSigma⟩
      · intro hshort
        exact ⟨one_infinite_tail_difference_upper p G γ k N hG hk.1 hk.2.1 hb.1 hk.2.2.1 hk.2.2.2,
          hSigma,one_infinite_tail_no_pi p G γ k N hG hr hk.1 hk.2.1 hb.1 hk.2.2.1 hk.2.2.2 hshort⟩
    · rintro ⟨a,b,hab,ha,hb'⟩
      exact ⟨⟨bounded_tail_scott_upper p G γ N hG hb.1,
        two_infinite_tail_no_raw_sigma G p hG hr γ N a b hab hb.1 ha hb'⟩,
        two_infinite_tail_no_difference G p hG hr γ N a b hab hb.1 ha hb'⟩
end LogicLineages.ModelsAlgebra.PGroups
