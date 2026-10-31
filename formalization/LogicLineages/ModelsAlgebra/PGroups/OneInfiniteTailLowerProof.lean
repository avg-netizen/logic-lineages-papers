module
public import LogicLineages.ModelsAlgebra.PGroups.OneInfiniteTailLowerTargets
public import LogicLineages.ModelsAlgebra.PGroups.TerminalAbsorptionProof
public import LogicLineages.ModelsAlgebra.PGroups.ProductSubgroupSplitProof
public import LogicLineages.ModelsAlgebra.PGroups.IntrinsicNormalForm
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary

private theorem source_images (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G]
    (k N : ℕ) (hk : 0 < k) (hkN : k ≤ N) (hb : ∀ g : G, p^N • g=0)
    (hm : Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (k-1) : AddSubgroup G)) = Cardinal.aleph0)
    (ho : ∀ j : ℕ, j<N → j≠k-1 → Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) < Cardinal.aleph0) :
    Finite (multipleImage G (p^k)) ∧ Infinite (multipleImage G (p^(k-1))) := by
  have hf := finite_tail_from_ranks p G N hb k hkN (fun j hkj hjN => ho j hjN (by omega))
  have hi := infinite_ulm_infinite_filtration p G (k-1) hm
  rw [finite_filtration_multiple_image G p k] at hf
  rw [finite_filtration_multiple_image G p (k-1)] at hi
  exact ⟨hf,hi⟩

theorem one_infinite_tail_no_pi : Targets.oneInfiniteTailNoPi := by
  classical
  intro p _ G _ _ γ k N hG rG hk hkN hN hm ho hn
  let S : AddSubgroup G := transfiniteFiltration p (Ordinal.omega0*γ)
  obtain ⟨hf,hi⟩ := source_images p S k N hk hkN hN hm ho
  obtain ⟨t,ell,s,r,hell,hr,⟨e⟩⟩ := intrinsic_full_shift_normal_form p S k N hk hkN hN hf hi
    (fun j hj => ho j (by omega) (by omega))
  let L := ∀ i : Fin t, ZMod (p^ell i)
  let R := ℕ →₀ ZMod (p^k)
  let U := UpperCyclicGroup p s r
  let A := R × U
  let ep : S ≃+ A × L := e.trans ((AddEquiv.prodAssoc : ((L×R)×U) ≃+ (L×(R×U))).trans (AddEquiv.prodComm : (L×A) ≃+ (A×L)))
  obtain ⟨K,T,hsplit,hdis,⟨eK⟩,⟨eT⟩,_⟩ := product_subgroup_split G A L S ep
  have hA (j : ℕ) (hj : j<k) :
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup A)) =
      if j+1=k then Cardinal.aleph0 else 0 := by
    have hz : Finset.univ.filter (fun i : Fin s => j+1 = r i) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have he := (Finset.mem_filter.mp hi).2
      have hri := (hr i).1
      omega
    change Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup (R×U))) = _
    rw [product_ulm_rank p R U j,infinite_cyclic_ulm_rank p k j,finite_cyclic_ulm_rank p s r j,
      hz,Finset.card_empty,Nat.cast_zero,add_zero]
  have hKinf : Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (k-1) : AddSubgroup K)) = Cardinal.aleph0 := by
    have hh := (isomorphism_ulm_rank K A eK p (k-1)).trans (hA (k-1) (by omega))
    simpa only [Nat.sub_add_cancel (by omega : 1≤k),if_pos rfl,ite_true] using hh
  have hTk : ∀ x : T, p^k • x=0 := by
    intro x
    apply eT.injective
    rw [map_nsmul,map_zero]
    funext i
    exact power_cyclic_annihilation p (ell i) k (hell i).2.le ((eT x) i)
  have hTb : ∀ x : T, p^((k-1)+1) • x=0 := by
    simpa only [Nat.sub_add_cancel (by omega : 1≤k)] using hTk
  obtain ⟨j,hj,hne⟩ := hn
  have hz : Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup K)) = 0 := by
    have hh := (isomorphism_ulm_rank K A eK p j).trans (hA j (by omega))
    simpa only [if_neg (by omega : j+1≠k)] using hh
  apply terminal_absorption_no_pi G p hG rG γ K T N (k-1) j hsplit hdis hN hKinf hTb
  intro he
  exact hne (he.trans hz)
end LogicLineages.ModelsAlgebra.PGroups
