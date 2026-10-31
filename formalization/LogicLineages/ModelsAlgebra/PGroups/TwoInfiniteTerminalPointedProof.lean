module
public import LogicLineages.ModelsAlgebra.PGroups.TwoInfiniteTerminalPointedTargets
public import LogicLineages.ModelsAlgebra.PGroups.TerminalAbsorptionPointedEvenProof
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirTerminalSplitProof
public import LogicLineages.ModelsAlgebra.PGroups.TwoReservoirExtraction
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirChain
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirStage
public import LogicLineages.ModelsAlgebra.PGroups.ReservoirRank
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary

private theorem countable_rank_bound (p : ℕ) (G : Type) [AddCommGroup G] [Countable G] (j : ℕ) :
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) ≤ Cardinal.aleph0 := by
  letI : Countable (UlmLayer p (finiteFiltration p j : AddSubgroup G)) :=
    (QuotientAddGroup.mk'_surjective (successorSocleSubgroup p (finiteFiltration p j : AddSubgroup G))).countable
  exact (rank_le_card (ZMod p) _).trans Cardinal.mk_le_aleph0

private theorem raise_bound (p k n : ℕ) (hkn : k≤n) (G : Type) [AddCommGroup G]
    (h : ∀ x : G, p^k • x=0) : ∀ x : G, p^n • x=0 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hkn
  intro x
  rw [pow_add,mul_nsmul,h,nsmul_zero]

theorem two_infinite_terminal_pointed : Targets.twoInfiniteTerminalPointed := by
  classical
  intro G _ _ p _ hG rG γ N a b hab hN ha hb n x
  let δ : Ordinal := Ordinal.omega0*γ
  let S : AddSubgroup G := transfiniteFiltration p δ
  obtain ⟨A,instA,hcount,hA,⟨e⟩⟩ := two_reservoir_extraction p S N a b hab hN ha hb
  letI := instA
  letI : Countable A := hcount
  let B := ZMod (p^(a.val+1))
  let C := ZMod (p^(b.val+1))
  let D : AddSubgroup G := AddSubgroup.closure (Set.range x)
  letI : Finite D := p_primary_finite_tuple_closure G p (Fact.out : p.Prime).ne_zero hG n x
  let E : AddSubgroup S := D.comap S.subtype
  let jE : E → D := fun y => ⟨y.val.val,y.property⟩
  letI : Finite E := Finite.of_injective jE (by
    intro y z h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : D => (w:G)) h)
  letI : Fintype E := Fintype.ofFinite E
  have hcover (y : E) := reservoir_cover A B C (e y.val)
  choose idx hidx using hcover
  let M := Finset.univ.sup idx
  have hE (y : E) : e y.val ∈ reservoirStage A B C M :=
    reservoir_monotone A B C (Finset.le_sup (Finset.mem_univ y)) (hidx y)
  have hB : ∀ y : B, p^(a.val+1) • y=0 :=
    power_cyclic_annihilation p (a.val+1) (a.val+1) le_rfl
  obtain ⟨K,T,hsplit,hdis,⟨eK⟩,hT,hcoords⟩ := reservoir_ambient_split G A B C S e M (p^(a.val+1)) hB
  have hret : D ⊓ S ≤ K := by
    intro y hy
    exact (hcoords ⟨y,hy.2⟩).mpr (hE ⟨⟨y,hy.2⟩,hy.1⟩)
  obtain ⟨er⟩ := reservoir_stage_isomorphism A B C M
  have hstage := isomorphism_ulm_rank (reservoirStage A B C M)
    (A × ((Fin M → B) × (ℕ →₀ C))) er p b.val
  rw [product_ulm_rank p A ((Fin M → B) × (ℕ →₀ C)) b.val,
    product_ulm_rank p (Fin M → B) (ℕ →₀ C) b.val,
    infinite_cyclic_ulm_rank p (b.val+1) b.val] at hstage
  simp only [if_pos rfl,ite_true] at hstage
  have hstageInf : Cardinal.aleph0 ≤
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p b.val : AddSubgroup (reservoirStage A B C M))) := by
    rw [hstage]
    exact (le_add_self : Cardinal.aleph0 ≤ _+Cardinal.aleph0).trans le_add_self
  have hKinf : Module.rank (ZMod p) (UlmLayer p (finiteFiltration p b.val : AddSubgroup K)) = Cardinal.aleph0 := by
    apply le_antisymm (countable_rank_bound p K b.val)
    rw [isomorphism_ulm_rank K (reservoirStage A B C M) eK p b.val]
    exact hstageInf
  have hTb := raise_bound p (a.val+1) (b.val+1) (by exact Nat.add_le_add_right hab.le 1) T hT
  have hbase := terminal_absorption_comparison G p hG rG γ K T N b.val hsplit hdis hN hKinf hTb
  obtain ⟨et⟩ := hbase.1
  have hlow := reservoir_stage_rank p A (a.val+1) (b.val+1) (by omega) (by exact Nat.add_lt_add_right hab 1)
    (by rw [show a.val+1-1=a.val from by omega]; exact hA) M
  rw [show a.val+1-1=a.val from by omega] at hlow
  have hKlow := (isomorphism_ulm_rank K (reservoirStage A B C M) eK p a.val).trans hlow
  have hneq : Module.rank (ZMod p) (UlmLayer p (finiteFiltration p a.val : AddSubgroup S)) ≠
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p a.val : AddSubgroup K)) := by
    intro he
    have hh : Cardinal.aleph0=(M:Cardinal) := ha.symm.trans (he.trans hKlow)
    exact (Cardinal.natCast_lt_aleph0 (n := M)).ne hh.symm
  have hqt := (isomorphism_ulm_rank (transfiniteFiltration p δ : AddSubgroup (G ⧸ T)) K et p a.val).trans hKlow
  have hshift := transfinite_tail_ulm_rank (G ⧸ T) p δ (a.val:Ordinal)
  rw [finite_ordinal_filtration (transfiniteFiltration p δ : AddSubgroup (G ⧸ T)) p a.val] at hshift
  refine ⟨T,M,?_,hshift.symm.trans hqt,hbase.2.2 a.val hneq,
    terminal_absorption_pointed_even G p hG rG γ K T N b.val hsplit hdis hN hKinf hTb n x hret⟩
  change T ≤ S
  rw [hsplit]
  exact le_sup_right
end LogicLineages.ModelsAlgebra.PGroups
