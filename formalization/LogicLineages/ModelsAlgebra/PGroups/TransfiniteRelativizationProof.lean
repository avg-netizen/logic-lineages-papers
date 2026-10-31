module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteRelativizationTargets
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteMembershipProof
public import LogicLineages.ModelsAlgebra.PGroups.PiFiniteGuardProof
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDual
public import Mathlib.Data.List.OfFn
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupBackAndForth GroupInfinitary
universe u

theorem relativized_dual_realization : Targets.relativizedDualRealization.{u} := by
  classical
  intro G _ S n φ
  induction φ with
  | qf q => intro a; rfl
  | disjEx s m matrix ih =>
    intro a
    simp only [Formula.dual,Formula.RealizeIn,ih,not_exists]
  | conjAll s m matrix ih =>
    intro a
    simp only [Formula.dual,Formula.RealizeIn,ih,not_forall]

theorem block_membership_guard : Targets.blockMembershipGuard.{u} := by
  classical
  intro p γ _ n m
  have hex (i : Fin m) := omega_block_membership_definable.{u} p γ (n+m) (.var (Fin.natAdd n i))
  choose φ hφ hsem using hex
  let fs := List.ofFn φ
  have hf : ∀ ψ ∈ fs, Complexity .pi (2*γ) ψ := by
    intro ψ hψ
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hψ
    exact hφ i
  obtain ⟨hc,hr⟩ := pi_finite_guard_exact.{u} (2*γ) (n+m) fs hf
  refine ⟨piFiniteGuard (2*γ) fs,hc,?_⟩
  intro G _ a
  rw [hr G a]
  constructor
  · intro h i
    exact (hsem i G a).mp (h (φ i) (List.mem_ofFn.mpr ⟨i,rfl⟩))
  · intro h ψ hψ
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hψ
    exact (hsem i G a).mpr (h i)

private theorem zero_rank_qf (side : Polarity) (n : ℕ) (φ : Formula n)
    (h : Complexity side (0:Ordinal.{0}) φ) : ∃ q : QF n, φ = .qf q := by
  cases h with
  | qf side q => exact ⟨q,rfl⟩
  | sigma hzero s m matrix β lower rank => exact (hzero rfl).elim
  | pi hzero s m matrix β lower rank => exact (hzero rfl).elim

private theorem sigma_one_relative (p : ℕ) (γ : Ordinal.{0}) [Countable γ.ToType]
    (n : ℕ) (φ : Formula n) (hφ : Complexity .sigma (1:Ordinal.{0}) φ) :
    ∃ ψ : Formula n, Complexity .sigma (2*γ+1) ψ ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        ψ.Realize a ↔ φ.RealizeIn (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) a := by
  classical
  generalize hlevel : (1:Ordinal.{0}) = α at hφ
  cases hφ with
  | qf side q => exact (one_ne_zero hlevel).elim
  | sigma hpos s m matrix β lower rank =>
    subst α
    have lower1 (i : s) : β i < 1 := lower i
    have hq (i : s) : ∃ q : QF (n+m i), matrix i = .qf q := by
      have hi := rank i
      rw [Order.lt_one_iff.mp (lower1 i)] at hi
      exact zero_rank_qf .pi _ _ hi
    choose q hq using hq
    have hg (i : s) := block_membership_guard.{u} p γ n (m i)
    choose guard hguard hguardsem using hg
    let mat (i : s) := piAndQF (guard i) (q i)
    let ψ : Formula n := countableDisjEx m mat
    refine ⟨ψ,countable_disj_ex_complexity (2*γ+1)
      (ne_of_gt (lt_of_le_of_lt zero_le (Order.lt_succ (2*γ)))) s n m mat (fun _ => 2*γ)
      (fun _ => Order.lt_succ _) (fun i => (pi_and_qf_exact.{u} _ _ _ _ (hguard i)).1),?_⟩
    intro G _ a
    rw [countable_disj_ex_realization]
    constructor
    · rintro ⟨i,d,hd⟩
      obtain ⟨hg,hq'⟩ := (pi_and_qf_exact.{u} _ _ _ _ (hguard i)).2 G (append a d) |>.mp hd
      have hm : ∀ j, d j ∈ (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) := by
        intro j
        simpa only [append,Fin.addCases_right] using (hguardsem i G (append a d)).mp hg j
      refine ⟨i,fun j => ⟨d j,hm j⟩,?_⟩
      rw [hq i]
      exact hq'
    · rintro ⟨i,d,hd⟩
      refine ⟨i,fun j => (d j:G),?_⟩
      apply ((pi_and_qf_exact.{u} _ _ _ _ (hguard i)).2 G _).mpr
      refine ⟨(hguardsem i G _).mpr ?_,?_⟩
      · intro j
        simpa only [append,Fin.addCases_right] using (d j).property
      · rw [hq i] at hd
        exact hd

private theorem pi_one_relative (p : ℕ) (γ : Ordinal.{0}) [Countable γ.ToType]
    (n : ℕ) (φ : Formula n) (hφ : Complexity .pi (1:Ordinal.{0}) φ) :
    ∃ ψ : Formula n, Complexity .pi (2*γ+1) ψ ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        ψ.Realize a ↔ φ.RealizeIn (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) a := by
  classical
  obtain ⟨ψ,hψ,hsem⟩ := sigma_one_relative.{u} p γ n φ.dual (dual_complexity .pi 1 n φ hφ)
  refine ⟨ψ.dual,dual_complexity .sigma _ _ _ hψ,?_⟩
  intro G _ a
  rw [dual_realization,hsem,relativized_dual_realization]
  exact not_not

private theorem pi_below_two_relative (p : ℕ) (γ : Ordinal.{0}) [Countable γ.ToType]
    (β : Ordinal.{0}) (hβ : β<2) (n : ℕ) (φ : Formula n) (hφ : Complexity .pi β φ) :
    ∃ ψ : Formula n, Complexity .pi (2*γ+1) ψ ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        ψ.Realize a ↔ φ.RealizeIn (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) a := by
  by_cases h0 : β=0
  · subst β
    obtain ⟨q,rfl⟩ := zero_rank_qf .pi n φ hφ
    exact ⟨piQF q,(pi_qf_padding.{u,0} (2*γ+1)
      (ne_of_gt (lt_of_le_of_lt zero_le (Order.lt_succ (2*γ)))) n q).1,
      fun G _ a => (pi_qf_padding.{u,0} (2*γ+1)
        (ne_of_gt (lt_of_le_of_lt zero_le (Order.lt_succ (2*γ)))) n q).2 G a⟩
  · have h1 : β=1 := le_antisymm (Order.lt_two_iff.mp hβ) (Order.one_le_iff_ne_zero.mpr h0)
    subst β
    exact pi_one_relative p γ n φ hφ

private theorem sigma_two_relative (p : ℕ) (γ : Ordinal.{0}) [Countable γ.ToType]
    (n : ℕ) (φ : Formula n) (hφ : Complexity .sigma (2:Ordinal.{0}) φ) :
    ∃ ψ : Formula n, Complexity .sigma (2*γ+2) ψ ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        ψ.Realize a ↔ φ.RealizeIn (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) a := by
  classical
  generalize hlevel : (2:Ordinal.{0}) = α at hφ
  cases hφ with
  | qf side q => exact (two_ne_zero hlevel).elim
  | sigma hpos s m matrix β lower rank =>
    subst α
    have lower2 (i : s) : β i < 2 := lower i
    have hm (i : s) := pi_below_two_relative.{u} p γ (β i) (lower2 i) (n+m i) (matrix i) (rank i)
    choose rel hrel hrelsem using hm
    have hg (i : s) := block_membership_guard.{u} p γ n (m i)
    choose guard hguard hguardsem using hg
    let mat (i : s) := piConjunction (piOneNormalize (guard i)) (rel i)
    have hmat (i : s) : Complexity .pi (2*γ+1) (mat i) :=
      pi_conjunction_complexity _ (ne_of_gt (lt_of_le_of_lt zero_le (Order.lt_succ (2*γ)))) _ _ _
        (pi_successor_padding.{u} _ _ _ (hguard i)).1 (hrel i)
    let ψ : Formula n := countableDisjEx m mat
    have hc : Complexity .sigma ((2*γ+1)+1) ψ := countable_disj_ex_complexity _
      (ne_of_gt (lt_of_le_of_lt zero_le (Order.lt_succ (2*γ+1)))) s n m mat (fun _ => 2*γ+1)
      (fun _ => Order.lt_succ _) hmat
    refine ⟨ψ,by simpa only [add_assoc,one_add_one_eq_two] using hc,?_⟩
    intro G _ a
    rw [countable_disj_ex_realization]
    constructor
    · rintro ⟨i,d,hd⟩
      obtain ⟨hg,hr⟩ := (pi_conjunction_realization G _ _ _ (append a d)).mp hd
      have hg' := (pi_one_normalization_realization G _ (guard i) _).mp hg
      have hm : ∀ j, d j ∈ (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) := by
        intro j
        simpa only [append,Fin.addCases_right] using (hguardsem i G (append a d)).mp hg' j
      exact ⟨i,fun j => ⟨d j,hm j⟩,(hrelsem i G (append a d)).mp hr⟩
    · rintro ⟨i,d,hd⟩
      refine ⟨i,fun j => (d j:G),?_⟩
      apply (pi_conjunction_realization G _ _ _ _).mpr
      refine ⟨(pi_one_normalization_realization G _ (guard i) _).mpr ?_,(hrelsem i G _).mpr hd⟩
      apply (hguardsem i G _).mpr
      intro j
      simpa only [append,Fin.addCases_right] using (d j).property

private theorem pi_two_relative (p : ℕ) (γ : Ordinal.{0}) [Countable γ.ToType]
    (n : ℕ) (φ : Formula n) (hφ : Complexity .pi (2:Ordinal.{0}) φ) :
    ∃ ψ : Formula n, Complexity .pi (2*γ+2) ψ ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        ψ.Realize a ↔ φ.RealizeIn (transfiniteFiltration p (Ordinal.omega0*γ) : AddSubgroup G) a := by
  classical
  obtain ⟨ψ,hψ,hsem⟩ := sigma_two_relative.{u} p γ n φ.dual (dual_complexity .pi 2 n φ hφ)
  refine ⟨ψ.dual,dual_complexity .sigma _ _ _ hψ,?_⟩
  intro G _ a
  rw [dual_realization,hsem,relativized_dual_realization]
  exact not_not

theorem low_transfinite_relativization : Targets.lowTransfiniteRelativization.{u} := by
  intro p γ _ side r hr n φ hφ
  rcases hr with rfl | rfl
  · cases side with
    | sigma => simpa only [Nat.cast_one] using sigma_one_relative.{u} p γ n φ (by simpa only [Nat.cast_one] using hφ)
    | pi => simpa only [Nat.cast_one] using pi_one_relative.{u} p γ n φ (by simpa only [Nat.cast_one] using hφ)
  · cases side with
    | sigma => simpa only [Nat.cast_ofNat] using sigma_two_relative.{u} p γ n φ hφ
    | pi => simpa only [Nat.cast_ofNat] using pi_two_relative.{u} p γ n φ hφ
end LogicLineages.ModelsAlgebra.PGroups
