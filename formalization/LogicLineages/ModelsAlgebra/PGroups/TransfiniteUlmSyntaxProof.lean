module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteUlmSyntaxTargets
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteRelativizationProof
public import LogicLineages.ModelsAlgebra.PGroups.UlmDimension
public import LogicLineages.ModelsAlgebra.PGroups.Relativized
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTailUlm
public import Mathlib.Data.Countable.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary

private theorem relative_sentence (G : Type) [AddCommGroup G] (S : AddSubgroup G) (φ : Formula 0) :
    φ.RealizeIn S (Fin.elim0 : Fin 0 → G) ↔ φ.Realize (Fin.elim0 : Fin 0 → S) := by
  have h := relativized_subgroup_agreement G S 0 φ (Fin.elim0 : Fin 0 → S)
  have he : (fun j : Fin 0 => ((Fin.elim0 j : S):G)) = Fin.elim0 := by
    funext j; exact Fin.elim0 j
  simpa only [he] using h

theorem transfinite_ulm_bounds_definable : Targets.transfiniteUlmBoundsDefinable := by
  intro p _ γ _ j m
  obtain ⟨lo,hlo,hlosem⟩ := low_transfinite_relativization.{0} p γ .sigma 2 (Or.inr rfl)
    0 (ulmLowerFormula p j 0 m) (ulm_lower_formula.{0,0} p j 0 m).1
  obtain ⟨hi,hhi,hhisem⟩ := low_transfinite_relativization.{0} p γ .pi 2 (Or.inr rfl)
    0 (ulmUpperFormula p j 0 m) (ulm_upper_rank_formula.{0,0} p j 0 m).1
  refine ⟨lo,hi,hlo,hhi,?_⟩
  intro G _
  let S : AddSubgroup G := transfiniteFiltration p (Ordinal.omega0*γ)
  have hrank := transfinite_tail_ulm_rank G p (Ordinal.omega0*γ) (j:Ordinal)
  rw [finite_ordinal_filtration] at hrank
  have hl := ulm_lower_rank_formula p j 0 m S (Fin.elim0 : Fin 0 → S)
  have hh := (ulm_upper_rank_formula.{0,0} p j 0 m).2 S (Fin.elim0 : Fin 0 → S)
  rw [hrank] at hl hh
  exact ⟨(hlosem G Fin.elim0).trans ((relative_sentence G S _).trans hl),
    (hhisem G Fin.elim0).trans ((relative_sentence G S _).trans hh)⟩

theorem transfinite_ulm_exact_definable : Targets.transfiniteUlmExactDefinable := by
  intro p _ γ _ j m
  obtain ⟨lo,hi,hlo,hhi,hsem⟩ := transfinite_ulm_bounds_definable p γ j m
  refine ⟨⟨lo,hi⟩,⟨hlo,hhi⟩,?_⟩
  intro G _
  change (lo.Realize Fin.elim0 ∧ hi.Realize Fin.elim0) ↔ _
  rw [(hsem G).1,(hsem G).2]
  constructor
  · rintro ⟨hl,hu⟩; exact le_antisymm hu hl
  · intro h; exact ⟨h.ge,h.le⟩

private theorem append_zero {G : Type} {n : ℕ} (a : Fin n → G) (c : Fin 0 → G) :
    append a c = a := by
  funext i
  change Fin.addCases a c (Fin.castAdd 0 i) = a i
  exact Fin.addCases_left _

theorem transfinite_ulm_infinite_definable : Targets.transfiniteUlmInfiniteDefinable := by
  classical
  intro p _ γ _ j
  have hex (m : ℕ) := transfinite_ulm_bounds_definable p γ j m
  choose lo hi hlo hhi hsem using hex
  let φ : Formula 0 := countableConjAll (fun _ : ℕ => 0) lo
  have hφ : Complexity .pi ((2*γ+2)+1) φ := countable_conj_all_complexity _
    (ne_of_gt (lt_of_le_of_lt zero_le (Order.lt_succ (2*γ+2)))) ℕ 0 _ _ (fun _ => 2*γ+2)
    (fun _ => Order.lt_succ _) hlo
  have hlevel : (2*γ+2)+1 = 2*γ+3 := by
    rw [add_assoc]
    congr 1
  refine ⟨φ,by rw [← hlevel]; exact hφ,?_⟩
  intro G _
  rw [countable_conj_all_realization,Cardinal.aleph0_le]
  constructor
  · intro h m
    exact (hsem m G).1.mp (by simpa only [append_zero] using h m Fin.elim0)
  · intro h m d
    simpa only [append_zero] using (hsem m G).1.mpr (h m)

theorem countable_transfinite_ulm_bound : Targets.countableTransfiniteUlmBound := by
  intro p _ G _ _ α
  letI : Countable (pSocle p (transfiniteFiltration p α : AddSubgroup G)) :=
    Subtype.val_injective.countable
  letI : Countable (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) :=
    (QuotientAddGroup.mk'_surjective (successorSocleSubgroup p (transfiniteFiltration p α : AddSubgroup G))).countable
  exact (rank_le_card (ZMod p) _).trans Cardinal.mk_le_aleph0
end LogicLineages.ModelsAlgebra.PGroups
