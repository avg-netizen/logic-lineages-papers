module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalAbsorptionRetainedTargets
public import LogicLineages.ModelsAlgebra.PGroups.TerminalAbsorptionProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary
private theorem raise_bound (p k n : ℕ) (hkn : k≤n) (G : Type) [AddCommGroup G]
    (h : ∀ x : G, p^k • x=0) : ∀ x : G, p^n • x=0 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hkn
  intro x
  rw [pow_add,mul_nsmul,h,nsmul_zero]

theorem terminal_absorption_retained : Targets.terminalAbsorptionRetained := by
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
  have hbase := terminal_deletion_odd G p hG rG γ K T k hsplit hdis hpos hSbound hw
  exact hbase.2.2.2.2.2
end LogicLineages.ModelsAlgebra.PGroups
