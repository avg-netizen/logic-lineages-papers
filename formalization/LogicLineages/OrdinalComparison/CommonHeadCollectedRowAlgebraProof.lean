module
public import LogicLineages.OrdinalComparison.CommonHeadCollectedRowTargets
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.Pairwise
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadCollectedRow.Proof
open CommonHeadLargeRow

private theorem indicator_sum {α : Type} [AddCommMonoid α] (ks : List Nat)
    (hn : ks.Nodup) (s : Nat) (v : α) :
    (ks.map (fun t => if s=t then v else 0)).sum = if s∈ks then v else 0 := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    obtain ⟨hk,ht⟩ := List.nodup_cons.mp hn
    by_cases he : s=k
    · subst s
      simp [hk,ih ht]
    · simp [he,ih ht]

private theorem keys_mem (row : Row) (a : Int×Nat) (ha : a∈row) : a.2∈keys row := by
  simp only [keys,List.mem_dedup]
  exact List.mem_map.mpr ⟨a,ha,rfl⟩

private theorem coeff_cons (a : Int×Nat) (row : Row) (t : Nat) :
    coefficient (a::row) t = (if a.2=t then a.1 else 0)+coefficient row t := by
  simp [coefficient]

private theorem sum_add {α β : Type} [AddCommMonoid β] (xs : List α) (f g : α → β) :
    (xs.map (fun x => f x+g x)).sum=(xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih]; ac_rfl

private theorem sum_le (xs : List Nat) (f g : Nat → Nat) (h : ∀ t∈xs, f t≤g t) :
    (xs.map f).sum≤(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add (h x List.mem_cons_self) (ih (fun t ht => h t (List.mem_cons_of_mem x ht)))

private theorem weighted_blocks (ks : List Nat) (hn : ks.Nodup) (row : Row)
    (hc : ∀ a∈row, a.2∈ks) (f : Nat → Int) :
    (ks.map (fun t => coefficient row t*f t)).sum=weighted f row := by
  induction row with
  | nil => simp [coefficient,weighted]
  | cons a row ih =>
    have hk := hc a List.mem_cons_self
    have hi := ih (fun b hb => hc b (List.mem_cons_of_mem a hb))
    have hw (t : Nat) : (if a.2=t then a.1 else 0)*f t =
        if a.2=t then a.1*f a.2 else 0 := by
      by_cases h : a.2=t
      · subst t; simp
      · simp [h]
    simp only [coeff_cons,add_mul]
    rw [sum_add]
    simp_rw [hw]
    rw [indicator_sum ks hn a.2 (a.1*f a.2), if_pos hk,hi]
    rfl

private theorem mass_blocks (ks : List Nat) (hn : ks.Nodup) (row : Row)
    (hc : ∀ a∈row, a.2∈ks) :
    (ks.map (fun t => (coefficient row t).natAbs)).sum≤mass row := by
  induction row with
  | nil => simp [coefficient,mass]
  | cons a row ih =>
    have hk := hc a List.mem_cons_self
    have hi := ih (fun b hb => hc b (List.mem_cons_of_mem a hb))
    have hbound : (ks.map (fun t => (coefficient (a::row) t).natAbs)).sum ≤
        (ks.map (fun t => (if a.2=t then a.1.natAbs else 0)+(coefficient row t).natAbs)).sum := by
      apply sum_le
      intro t ht
      rw [coeff_cons]
      have h := Int.natAbs_add_le (if a.2=t then a.1 else 0) (coefficient row t)
      by_cases he : a.2=t <;> simpa [he] using h
    rw [sum_add,indicator_sum ks hn a.2 a.1.natAbs,if_pos hk] at hbound
    exact hbound.trans (Nat.add_le_add_left hi a.1.natAbs)

private theorem filter_zero_sum {α : Type} [AddCommMonoid α] (row : Row) (f : Int×Nat → α)
    (hz : ∀ a, a.1=0 → f a=0) :
    ((row.filter (fun a => a.1 != 0)).map f).sum=(row.map f).sum := by
  induction row with
  | nil => simp
  | cons a row ih =>
    by_cases ha : a.1=0
    · simp [ha,hz a ha,ih]
    · simp [ha,ih]

theorem exactWeightedCollection : Targets.ExactWeightedCollection := by
  intro row f
  unfold collect weighted
  rw [filter_zero_sum _ _ (by intro a ha; simp [ha])]
  simp only [List.map_map,Function.comp_def]
  exact weighted_blocks (keys row) (List.nodup_dedup _) row (keys_mem row) f

theorem literalCollectedSupport : Targets.LiteralCollectedSupport := by
  intro row
  refine ⟨?_,?_,?_⟩
  · unfold collect
    apply List.Pairwise.filter
    rw [List.pairwise_map]
    exact List.nodup_dedup _
  · intro a ha
    obtain ⟨hm,hne⟩ := List.mem_filter.mp ha
    obtain ⟨t,ht,he⟩ := List.mem_map.mp hm
    subst a
    have hp : t∈row.map Prod.snd := List.mem_dedup.mp ht
    obtain ⟨b,hb,heq⟩ := List.mem_map.mp hp
    exact ⟨by simpa using hne,rfl,b,hb,heq⟩
  · unfold collect mass
    rw [filter_zero_sum _ _ (by intro a ha; simp [ha])]
    simp only [List.map_map,Function.comp_def]
    exact mass_blocks (keys row) (List.nodup_dedup _) row (keys_mem row)
end LogicLineages.OrdinalComparison.CommonHeadCollectedRow.Proof
