module

public import LogicLineages.ModelsAlgebra.PGroups.SocleUlmVanishingTargets
public import LogicLineages.ModelsAlgebra.PGroups.SocleRoot
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.Torsion.Field

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

universe u v

theorem ulm_rank_zero_socle : Targets.groupUlmRankZeroSocle.{u} := by
  intro p _ G _ S
  constructor
  · intro hrank
    letI : Subsingleton (UlmLayer p S) :=
      (rank_zero_iff (R := ZMod p) (M := UlmLayer p S)).mp hrank
    intro x hx
    let y : pSocle p S := ⟨x, hx⟩
    have hzero : (y : UlmLayer p S) = 0 := Subsingleton.elim _ _
    exact ((QuotientAddGroup.eq_zero_iff y).mp hzero).1
  · intro h
    apply (rank_zero_iff (R := ZMod p) (M := UlmLayer p S)).mpr
    have hzero : ∀ z : UlmLayer p S, z = 0 := by
      intro z
      obtain ⟨x, rfl⟩ := (QuotientAddGroup.mk'_surjective (successorSocleSubgroup p S)) z
      exact (QuotientAddGroup.eq_zero_iff x).mpr ⟨h x.property, x.property.2⟩
    exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩

private theorem finite_filtration_antitone (G : Type u) [AddCommGroup G] (p : ℕ) :
    Antitone (fun j => (finiteFiltration p j : AddSubgroup G)) := by
  apply antitone_nat_of_succ_le
  intro j
  rintro x ⟨y, hy, rfl⟩
  exact (finiteFiltration p j : AddSubgroup G).nsmul_mem hy p

theorem socle_root_ulm_vanishing : Targets.groupSocleRootUlmVanishing.{u} := by
  intro p _ G _ j
  constructor
  · intro h i hi
    apply (ulm_rank_zero_socle p G (finiteFiltration p i)).mpr
    intro x hx
    have hxj := h (show x ∈ pSocle p (⊤ : AddSubgroup G) from ⟨by trivial, hx.2⟩)
    exact finite_filtration_antitone G p (Nat.succ_le_of_lt hi) hxj
  · intro h
    have go : ∀ k : ℕ,
        (∀ i : ℕ, i < k → Module.rank (ZMod p)
          (UlmLayer p (finiteFiltration p i : AddSubgroup G)) = 0) →
        pSocle p (⊤ : AddSubgroup G) ≤ finiteFiltration p k := by
      intro k
      induction k with
      | zero =>
        intro _ x hx
        trivial
      | succ k ih =>
        intro hall x hx
        have hxk := ih (fun i hi => hall i (Nat.lt_succ_of_lt hi)) hx
        exact (ulm_rank_zero_socle p G (finiteFiltration p k)).mp
          (hall k (Nat.lt_succ_self k)) ⟨hxk, hx.2⟩
    exact go j h

theorem socle_root_vanishing_formula : Targets.groupSocleRootVanishingFormula.{u,v} := by
  intro p _ j n
  refine ⟨(socle_root_formula.{u,v} p j n).1, ?_⟩
  intro G _ a
  exact ((socle_root_formula.{u,v} p j n).2 G a).trans (socle_root_ulm_vanishing p G j)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
