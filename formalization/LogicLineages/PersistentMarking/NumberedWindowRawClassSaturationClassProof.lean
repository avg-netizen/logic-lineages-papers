module
public import LogicLineages.PersistentMarking.NumberedWindowRawClassSaturationTargets

public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawClassSaturationClassProof
open NumberedWindowClassAlgorithm
open NumberedWindowRawClassSaturationTargets

private theorem seenIff {step : Nat → Nat → Bool} {pool seen : List Nat} {v : Nat} :
    v ∈ advance step pool seen ↔ v ∈ pool ∧ ∃ w, w ∈ seen ∧ (w = v ∨ step w v = true) := by
  simp only [advance,List.mem_filter,List.any_eq_true,Bool.or_eq_true,beq_iff_eq]

private theorem seedIff {step : Nat → Nat → Bool} {pool : List Nat} {seed v : Nat} :
    v ∈ rounds step pool seed 0 ↔ v ∈ pool ∧ seed = v := by
  simp only [rounds,List.mem_filter,beq_iff_eq]

private theorem roundSublist (step : Nat → Nat → Bool) (pool : List Nat) (seed fuel : Nat) :
    List.Sublist (rounds step pool seed fuel) pool := by
  cases fuel with
  | zero => exact List.filter_sublist
  | succ n => exact List.filter_sublist

private theorem monoFilter (p q : Nat → Bool) (pool : List Nat)
    (h : ∀ v, v ∈ pool → p v = true → q v = true) :
    List.Sublist (pool.filter p) (pool.filter q) := by
  induction pool with
  | nil => exact .slnil
  | cons a tail ih =>
    have hTail := ih (fun v hv hp => h v (List.mem_cons_of_mem a hv) hp)
    by_cases hp : p a = true
    · have hq := h a List.mem_cons_self hp
      rw [List.filter_cons_of_pos hp,List.filter_cons_of_pos hq]
      exact .cons_cons a hTail
    · by_cases hq : q a = true
      · rw [List.filter_cons_of_neg hp,List.filter_cons_of_pos hq]
        exact .cons a hTail
      · rw [List.filter_cons_of_neg hp,List.filter_cons_of_neg hq]
        exact hTail

private theorem extendSeen (step : Nat → Nat → Bool) (pool a b : List Nat)
    (h : ∀ x ∈ a, x ∈ b) : List.Sublist (advance step pool a) (advance step pool b) := by
  unfold advance
  apply monoFilter
  intro v _ hv
  obtain ⟨w,seen,actual⟩ := List.any_eq_true.mp hv
  exact List.any_eq_true.mpr ⟨w,h w seen,actual⟩

private theorem roundStep (step : Nat → Nat → Bool) (pool : List Nat) (seed fuel : Nat) :
    List.Sublist (rounds step pool seed fuel) (rounds step pool seed (fuel+1)) := by
  induction fuel with
  | zero =>
    change List.Sublist (pool.filter (fun x => seed == x))
      (advance step pool (pool.filter (fun x => seed == x)))
    unfold advance
    apply monoFilter
    intro v inPool bit
    have first : v ∈ pool.filter (fun x => seed == x) := List.mem_filter.mpr ⟨inPool,bit⟩
    exact List.any_eq_true.mpr ⟨v,first,by simp⟩
  | succ n ih =>
    change List.Sublist (advance step pool (rounds step pool seed n))
      (advance step pool (rounds step pool seed (n+1)))
    exact extendSeen step pool _ _ (fun _ hv => ih.subset hv)

private theorem fixedNext (step : Nat → Nat → Bool) (pool : List Nat) (seed n : Nat)
    (h : rounds step pool seed n = rounds step pool seed (n+1)) :
    rounds step pool seed (n+1) = rounds step pool seed ((n+1)+1) := by
  change advance step pool (rounds step pool seed n) =
    advance step pool (rounds step pool seed (n+1))
  rw [h]

private theorem fixedThrough (step : Nat → Nat → Bool) (pool : List Nat) (seed : Nat)
    {n fuel : Nat} (within : n ≤ fuel)
    (h : rounds step pool seed n = rounds step pool seed (n+1)) :
    rounds step pool seed fuel = rounds step pool seed (fuel+1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le within
  clear within
  induction k with
  | zero => exact h
  | succ k ih => exact fixedNext step pool seed (n+k) ih

private theorem lengthBound (step : Nat → Nat → Bool) (pool : List Nat) (seed : Nat) :
    advance step pool (members step pool seed) = members step pool seed := by
  apply Classical.byContradiction
  intro notFixed
  have nofix (n : Nat) (before : n ≤ pool.length) :
      rounds step pool seed n ≠ rounds step pool seed (n+1) := by
    intro eq
    exact notFixed (fixedThrough step pool seed before eq).symm
  have growth (n : Nat) : n ≤ pool.length + 1 → n ≤ (rounds step pool seed n).length := by
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have before : n ≤ pool.length := by omega
      have prior : n ≤ (rounds step pool seed n).length := ih (by omega)
      have sub := roundStep step pool seed n
      have len := sub.length_le
      have neq : (rounds step pool seed n).length ≠ (rounds step pool seed (n+1)).length := by
        intro eq
        exact nofix n before (sub.eq_of_length eq)
      omega
  have long := growth (pool.length+1) (Nat.le_refl _)
  have small := (roundSublist step pool seed (pool.length+1)).length_le
  omega

theorem exactSaturation : ExactLiteralClassSaturation :=
  fun step pool seed => ⟨roundSublist step pool seed,roundStep step pool seed,lengthBound step pool seed⟩

private theorem seedStays (step : Nat → Nat → Bool) (pool : List Nat) (y : Nat)
    (inPool : y ∈ pool) : ∀ fuel, y ∈ rounds step pool y fuel := by
  intro fuel
  induction fuel with
  | zero => exact seedIff.mpr ⟨inPool,rfl⟩
  | succ fuel ih => exact (roundStep step pool y fuel).subset ih

/-- A predicate paid at the seed and by each genuine edge is paid for
every actual round member. Stutters preserve the identical raw value. -/
theorem roundsProperty (step : Nat → Nat → Bool) (pool : List Nat) (seed : Nat)
    (P : Nat → Prop) (atSeed : P seed)
    (forward : ∀ a b, P a → step a b = true → P b) (fuel : Nat) :
    ∀ y ∈ rounds step pool seed fuel, P y := by
  induction fuel with
  | zero =>
    intro y hy
    have eq := (seedIff.mp hy).2
    exact eq ▸ atSeed
  | succ n ih =>
    intro y hy
    have late : y ∈ advance step pool (rounds step pool seed n) := hy
    obtain ⟨_,a,hA,sameOrStep⟩ := seenIff.mp late
    rcases sameOrStep with same | goes
    · exact same ▸ ih a hA
    · exact forward a y (ih a hA) goes

theorem exactSamePool : ExactSamePoolLeastSelf := by
  intro step pool seed y h
  change (members step pool seed).min? = some y at h
  obtain ⟨oldMember,oldBound⟩ := List.min?_eq_some_iff.mp h
  have inPool : y ∈ pool := (roundSublist step pool seed pool.length).subset oldMember
  have within (fuel : Nat) : ∀ v ∈ rounds step pool y fuel, v ∈ members step pool seed := by
    induction fuel with
    | zero =>
      intro v hv
      exact (seedIff.mp hv).2 ▸ oldMember
    | succ n ih =>
      intro v hv
      have stepMem : v ∈ advance step pool (rounds step pool y n) := hv
      obtain ⟨vPool,a,ha,via⟩ := seenIff.mp stepMem
      rw [← lengthBound step pool seed]
      exact seenIff.mpr ⟨vPool,a,ih a ha,via⟩
  change (members step pool y).min? = some y
  apply List.min?_eq_some_iff.mpr
  exact ⟨seedStays step pool y inPool pool.length,
    fun v hv => oldBound v (within pool.length v hv)⟩

end LogicLineages.PersistentMarking.NumberedWindowRawClassSaturationClassProof
