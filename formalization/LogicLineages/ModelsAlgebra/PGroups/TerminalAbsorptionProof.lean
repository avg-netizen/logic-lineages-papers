module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalAbsorptionTargets
public import LogicLineages.ModelsAlgebra.PGroups.TerminalDeletionEvenProof
public import LogicLineages.ModelsAlgebra.PGroups.SubgroupSumProductProof
public import LogicLineages.ModelsAlgebra.PGroups.BackForthIsomorphismProof
public import LogicLineages.ModelsAlgebra.PGroups.SourceAbsorption
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTail
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTailUlm
public import LogicLineages.ModelsAlgebra.PGroups.UlmEquivalenceTransport
public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestriction
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary

private theorem raise_bound (p k n : ℕ) (hkn : k≤n) (G : Type) [AddCommGroup G]
    (h : ∀ x : G, p^k • x=0) : ∀ x : G, p^n • x=0 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hkn
  intro x
  rw [pow_add,mul_nsmul,h,nsmul_zero]

private theorem rank_invariant (p : ℕ) (G H : Type) [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (α : Ordinal.{0}) :
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) =
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H)) := by
  have hk : e.toAddMonoidHom.ker ≤ (transfiniteFiltration p α : AddSubgroup G) := by
    rw [e.toAddMonoidHom.ker_eq_bot e.injective]
    exact bot_le
  have hm := map_transfiniteFiltration_below p e.toAddMonoidHom e.surjective α hk α le_rfl
  have hu := injective_ulm_isomorphism G H p (transfiniteFiltration p α) e.toAddMonoidHom e.injective
  rw [hm] at hu
  obtain ⟨u⟩ := hu
  exact u.rank_eq

theorem terminal_absorption_comparison : Targets.terminalAbsorptionComparison := by
  classical
  intro G _ _ p _ hG rG γ K T N b hsplit hdis hN hRank hT
  let δ : Ordinal := Ordinal.omega0*γ
  let S : AddSubgroup G := transfiniteFiltration p δ
  have hK : K ≤ S := by
    change K ≤ transfiniteFiltration p (Ordinal.omega0*γ)
    rw [hsplit]
    exact le_sup_left
  have hNK : ∀ x : K, p^N • x=0 := by
    intro x
    exact Subtype.ext (congrArg (fun z : S => (z:G)) (hN ⟨x,hK x.property⟩))
  letI : Infinite (finiteFiltration p b : AddSubgroup K) := infinite_ulm_infinite_filtration p K b hRank
  letI : Infinite K := Infinite.of_injective (fun x : (finiteFiltration p b : AddSubgroup K) => (x:K)) Subtype.val_injective
  have hex : ∃ k : ℕ, ∀ x : K, p^k • x=0 := ⟨N,hNK⟩
  let k := Nat.find hex
  have hk : ∀ x : K, p^k • x=0 := Nat.find_spec hex
  have hpos : 0<k := by
    apply Nat.pos_of_ne_zero
    intro hz
    obtain ⟨x,hx⟩ := exists_ne (0:K)
    exact hx (by simpa only [hz,pow_zero,one_nsmul] using hk x)
  have hbk : b<k := by
    by_contra h
    have hz := raise_bound p k b (le_of_not_gt h) K hk
    obtain ⟨x,hx⟩ := exists_ne (0:(finiteFiltration p b : AddSubgroup K))
    obtain ⟨y,hy⟩ := (finite_filtration_multiple_image K p b).le x.property
    change p^b • y = (x:K) at hy
    exact hx (Subtype.ext (hy.symm.trans (hz y)))
  have hTk := raise_bound p (b+1) k (Nat.succ_le_of_lt hbk) T hT
  obtain ⟨es,hes⟩ := subgroup_sum_product G S K T hsplit hdis
  have hSbound : ∀ x : S, p^k • x=0 := by
    intro x
    obtain ⟨⟨a,c⟩,rfl⟩ := es.surjective x
    rw [← map_nsmul]
    have hz : p^k • (a,c) = (0:K×T) := Prod.ext (hk a) (hTk c)
    rw [hz,map_zero]
  have hw : ∃ x : K, p^(k-1) • x≠0 := not_forall.mp (Nat.find_min hex (Nat.sub_lt hpos (by decide : 0<1)))
  have htwo := (source_bounded_absorption p K T k ⟨b,hbk⟩ hk hRank hT).2
  have htwoS : BackAndForth (2:Ordinal) (Fin.elim0 : Fin 0 → S) (Fin.elim0 : Fin 0 → K) := by
    have hh := (back_forth_isomorphism 2 (K×T) K S K es (AddEquiv.refl K) 0 Fin.elim0 Fin.elim0).mp htwo
    convert hh using 1 <;> funext i <;> exact Fin.elim0 i
  have hbase := terminal_deletion_odd G p hG rG γ K T k hsplit hdis hpos hSbound hw
  obtain ⟨et⟩ := hbase.2.1
  refine ⟨⟨et⟩,terminal_deletion_even G p hG rG γ K T k hsplit hdis hpos hSbound hw htwoS,?_⟩
  intro j hne he
  obtain ⟨e⟩ := he
  have hh := rank_invariant p G (G ⧸ T) e (δ+j)
  rw [← transfinite_tail_ulm_rank G p δ (j:Ordinal),← transfinite_tail_ulm_rank (G ⧸ T) p δ (j:Ordinal)] at hh
  rw [finite_ordinal_filtration S p j,
    finite_ordinal_filtration (transfiniteFiltration p δ : AddSubgroup (G ⧸ T)) p j] at hh
  exact hne (hh.trans (isomorphism_ulm_rank _ K et p j))

theorem terminal_absorption_no_pi : Targets.terminalAbsorptionNoPi := by
  intro G _ _ p _ hG rG γ K T N b j hsplit hdis hN hRank hT hne φ hc hs
  have hh := terminal_absorption_comparison G p hG rG γ K T N b hsplit hdis hN hRank hT
  letI : Countable (G ⧸ T) := (QuotientAddGroup.mk'_surjective T).countable
  have hScott := raw_scott_restriction G φ hs
  have ht := (truth_transfer (2*γ+2) G (G ⧸ T) 0 Fin.elim0 Fin.elim0 hh.2.1).1 φ hc hScott.1
  exact hh.2.2 j hne (hScott.2 (G ⧸ T) ht)
end LogicLineages.ModelsAlgebra.PGroups
