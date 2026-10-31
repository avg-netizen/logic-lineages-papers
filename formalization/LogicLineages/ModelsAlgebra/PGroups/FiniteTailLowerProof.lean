module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteTailLowerTargets
public import LogicLineages.ModelsAlgebra.PGroups.ZeroTailDeletionProof
public import LogicLineages.ModelsAlgebra.PGroups.RawScottRestriction
public import LogicLineages.ModelsAlgebra.PGroups.Infinitary
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary

private theorem finite_primary_bound (G : Type) [AddCommGroup G] [Finite G] (p : ℕ)
    (hp : ∀ x : G, ∃ k : ℕ, p^k • x=0) : ∃ N : ℕ, ∀ x : G, p^N • x=0 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  choose k hk using hp
  refine ⟨Finset.univ.sup k,?_⟩
  intro x
  have hle : k x ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ x)
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hle
  rw [hj,pow_add,mul_nsmul,hk,nsmul_zero]

theorem finite_tail_no_pi : Targets.finiteTailNoPi := by
  intro G _ _ p _ hG rG γ hγ hfinite hne φ hc hs
  let S : AddSubgroup G := transfiniteFiltration p (Ordinal.omega0*γ)
  letI : Finite S := hfinite
  have hprimary : ∀ x : S, ∃ k : ℕ, p^k • x=0 := by
    intro x
    obtain ⟨k,hk⟩ := hG x
    exact ⟨k,Subtype.ext hk⟩
  obtain ⟨N,hN⟩ := finite_primary_bound S p hprimary
  have hlong : StagesNonzeroBelow p G (Ordinal.omega0*γ) := by
    intro α hα hz
    apply hne
    exact le_antisymm ((transfiniteFiltration_antitone p hα.le).trans hz.le) bot_le
  obtain ⟨hcount,_,_,_,_,_,hbf,hnon⟩ := zero_tail_deletion G p hG rG γ hγ hlong N hN
  letI : Countable (G ⧸ S) := hcount
  have hScott := raw_scott_restriction G φ hs
  have ht := (truth_transfer (2*γ+1) G (G ⧸ S) 0 Fin.elim0 Fin.elim0 hbf).1 φ hc hScott.1
  exact hnon hne (hScott.2 (G ⧸ S) ht)
end LogicLineages.ModelsAlgebra.PGroups
