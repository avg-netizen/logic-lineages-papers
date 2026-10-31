module
public import LogicLineages.ModelsAlgebra.PGroups.ThreeRelativizationTargets
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteRelativizationProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary
universe u

private theorem pi_below_three_relative (p : ℕ) (γ : Ordinal.{0}) [Countable γ.ToType]
    (β : Ordinal.{0}) (hβ : β < 3) (n : ℕ) (φ : Formula n)
    (hφ : Complexity .pi β φ) :
    ∃ ψ : Formula n, Complexity .pi (2*γ+2) ψ ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        ψ.Realize a ↔ φ.RealizeIn (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) a := by
  by_cases h0 : β=0
  · subst β
    have hq : ∃ q : QF n, φ = .qf q := by
      cases hφ with
      | qf side q => exact ⟨q,rfl⟩
      | pi hzero s m matrix β lower rank => exact (hzero rfl).elim
    obtain ⟨q,rfl⟩ := hq
    exact ⟨piQF q,(pi_qf_padding.{u,0} (2*γ+2) (by positivity) n q).1,
      fun G _ a => (pi_qf_padding.{u,0} (2*γ+2) (by positivity) n q).2 G a⟩
  · have hb : β ≤ 2 := by simpa only [Order.succ_eq_add_one] using (Order.le_of_lt_succ hβ)
    have hh := positive_complexity_monotone .pi β 2 n φ h0 hb hφ
    exact low_transfinite_relativization.{u} p γ .pi 2 (Or.inr rfl) n φ hh

private theorem sigma_three_relative (p : ℕ) (γ : Ordinal.{0}) [Countable γ.ToType]
    (n : ℕ) (φ : Formula n) (hφ : Complexity .sigma (3:Ordinal.{0}) φ) :
    ∃ ψ : Formula n, Complexity .sigma (2*γ+3) ψ ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        ψ.Realize a ↔ φ.RealizeIn (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) a := by
  classical
  generalize hlevel : (3:Ordinal.{0}) = α at hφ
  cases hφ with
  | qf side q => exact ((by norm_num : (3:Ordinal.{0}) ≠ 0) hlevel).elim
  | sigma hpos s m matrix β lower rank =>
    subst α
    have lower2 (i : s) : β i < 3 := lower i
    have hm (i : s) := pi_below_three_relative.{u} p γ (β i) (lower2 i) (n+m i) (matrix i) (rank i)
    choose rel hrel hrelsem using hm
    have hg (i : s) := block_membership_guard.{u} p γ n (m i)
    choose guard hguard hguardsem using hg
    let mat (i : s) := piConjunction (piOneNormalize (piOneNormalize (guard i))) (rel i)
    have hmat (i : s) : Complexity .pi (2*γ+2) (mat i) :=
      pi_conjunction_complexity (2*γ+2) (by positivity) _ _ _
        (by simpa only [add_assoc,one_add_one_eq_two] using
          (pi_successor_padding.{u} _ _ _ (pi_successor_padding.{u} _ _ _ (hguard i)).1).1) (hrel i)
    let ψ : Formula n := countableDisjEx m mat
    have hc : Complexity .sigma ((2*γ+2)+1) ψ := countable_disj_ex_complexity _
      (ne_of_gt (lt_of_le_of_lt zero_le (Order.lt_succ (2*γ+2)))) s n m mat (fun _ => 2*γ+2)
      (fun _ => Order.lt_succ _) hmat
    refine ⟨ψ,by simpa only [add_assoc, show (2:Ordinal.{0})+1=3 from by norm_num] using hc,?_⟩
    intro G _ a
    rw [countable_disj_ex_realization]
    constructor
    · rintro ⟨i,d,hd⟩
      obtain ⟨hg,hr⟩ := (pi_conjunction_realization G _ _ _ (append a d)).mp hd
      have hg' := (pi_one_normalization_realization G _ (guard i) _).mp
        ((pi_one_normalization_realization G _ (piOneNormalize (guard i)) _).mp hg)
      have hm : ∀ j, d j ∈ (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) := by
        intro j
        simpa only [append,Fin.addCases_right] using (hguardsem i G (append a d)).mp hg' j
      exact ⟨i,fun j => ⟨d j,hm j⟩,(hrelsem i G (append a d)).mp hr⟩
    · rintro ⟨i,d,hd⟩
      refine ⟨i,fun j => (d j:G),?_⟩
      apply (pi_conjunction_realization G _ _ _ _).mpr
      refine ⟨(pi_one_normalization_realization G _ (piOneNormalize (guard i)) _).mpr
        ((pi_one_normalization_realization G _ (guard i) _).mpr ?_),(hrelsem i G _).mpr hd⟩
      apply (hguardsem i G _).mpr
      intro j
      simpa only [append,Fin.addCases_right] using (d j).property


theorem three_transfinite_relativization : Targets.threeTransfiniteRelativization.{u} := by
  intro p γ _ side n φ hφ
  cases side with
  | sigma => exact sigma_three_relative.{u} p γ n φ hφ
  | pi =>
    obtain ⟨ψ,hψ,hsem⟩ := sigma_three_relative.{u} p γ n φ.dual (dual_complexity .pi 3 n φ hφ)
    refine ⟨ψ.dual,dual_complexity .sigma _ _ _ hψ,?_⟩
    intro G _ a
    rw [dual_realization,hsem,relativized_dual_realization]
    exact not_not
end LogicLineages.ModelsAlgebra.PGroups
