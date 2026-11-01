module
public import LogicLineages.ModelsAlgebra.PGroups.OddObstructionCompleteTargets
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleOddSigmaProof
public import LogicLineages.ModelsAlgebra.PGroups.ShortSigmaCollapseProof
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleSplittingProof
public import LogicLineages.ModelsAlgebra.PGroups.ReducedLengthProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary GroupBackAndForth

theorem odd_long_source_no_sigma : Targets.oddLongSourceNoSigma := by
  intro p _ R D _ _ _ _ γ _ ell hR hD hred hd hγ hlen hlong
  exact divisible_product_odd_no_raw_sigma R D p hR hD hred hd γ hγ
    (fun ξ hξ=>hlen.2 ξ (hξ.trans_le hlong))

theorem odd_primary_sigma_lowering : Targets.oddPrimarySigmaLowering := by
  classical
  intro p _ G _ _ γ _ hG hγ φ hφ hScott
  obtain ⟨r,R,_,_,hred,_,_,e,_⟩ := actual_divisible_splitting G
  let D : AddSubgroup G := divisiblePart G
  have hR : ∀x:R,∃k:ℕ,p^k • x=0 := by
    intro x
    obtain ⟨k,hk⟩ := hG (x:G)
    exact ⟨k,Subtype.ext hk⟩
  have hD : ∀x:D,∃k:ℕ,p^k • x=0 := by
    intro x
    obtain ⟨k,hk⟩ := hG (x:G)
    exact ⟨k,Subtype.ext hk⟩
  have hd : GroupDivisible D := (actual_divisible_part G).1
  obtain ⟨ell,hell,_⟩ := countable_reduced_exact_length R p hR hred
  obtain ⟨_,hmem,_⟩ := divisible_product_data R D p hR hD hd
  by_cases hlt:ell<Ordinal.omega0*γ
  · have hznext : (transfiniteFiltration p (ell+1):AddSubgroup R)=⊥ := by
      apply le_antisymm _ bot_le
      exact (transfiniteFiltration_antitone p (show ell≤ell+1 from le_self_add)).trans
        (le_of_eq hell.2.1)
    have hsP : (transfiniteFiltration p ell:AddSubgroup (R×D))=
        transfiniteFiltration p (ell+1) := by
      apply AddSubgroup.ext
      intro x
      rw [hmem ell x,hmem (ell+1) x,hell.2.1,hznext]
    have hmap (β:Ordinal.{0}) :
        (transfiniteFiltration p β:AddSubgroup (R×D)).map e.toAddMonoidHom=
          (transfiniteFiltration p β:AddSubgroup G) := by
      have hk : e.toAddMonoidHom.ker≤(transfiniteFiltration p β:AddSubgroup (R×D)) := by
        rw [e.toAddMonoidHom.ker_eq_bot e.injective]
        exact bot_le
      exact map_transfiniteFiltration_below p e.toAddMonoidHom e.surjective β hk β le_rfl
    have hsG : StableAt p G ell := by
      change (transfiniteFiltration p ell:AddSubgroup G)=transfiniteFiltration p (ell+1)
      rw [←hmap ell,←hmap (ell+1),hsP]
    exact short_stable_raw_sigma_scott_lowering p G γ ell hγ hell.1 hG hlt hsG φ hφ hScott
  · have hlong : StagesNonzeroBelow p R (Ordinal.omega0*γ) :=
      fun ξ hξ=>hell.2.2 ξ (hξ.trans_le (le_of_not_gt hlt))
    have hs := raw_scott_restriction G φ hScott
    have hbf := comparison_isomorphism (2*γ+1) (R×D) G e 0 Fin.elim0
    have hnil : (fun i:Fin 0=>e (Fin.elim0 i))=(Fin.elim0:Fin 0→G) := by
      funext i
      exact Fin.elim0 i
    rw [hnil] at hbf
    have hsP : GroupScottSentence (R×D) φ := by
      refine ⟨(truth_transfer (2*γ+1) (R×D) G 0 Fin.elim0 Fin.elim0 hbf).2 φ hφ hs.1,?_⟩
      intro H _ _ ht
      obtain ⟨u⟩ := hs.2 H ht
      exact ⟨e.trans u⟩
    exact (divisible_product_odd_no_sigma R D p hR hD hred hd γ hγ hlong φ hφ hsP).elim

theorem odd_obstruction_full_source : Targets.oddObstructionFullSource :=
  ⟨odd_long_source_no_sigma,odd_primary_sigma_lowering⟩

end LogicLineages.ModelsAlgebra.PGroups
