module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmClassRankProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmCollisionProof
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
open PolynomialGraphCompletion Algorithm

theorem rowAdd_value (r s : Row) (ν : Nat → Nat) :
    RowValue (rowAdd r s) ν = RowValue r ν+RowValue s ν := by
  simp only [rowAdd,RowValue,List.map_append,List.sum_append]
  ring

theorem foldRows_value (rows : List Row) (ν : Nat → Nat) :
    RowValue (rows.foldr rowAdd (0,[])) ν = (rows.map (fun r => RowValue r ν)).sum := by
  induction rows with
  | nil => simp [RowValue]
  | cons r rows ih => simp [rowAdd_value,ih]

theorem foldRows_allowed (D : Nat) (rows : List Row) (h : ∀ r ∈ rows, RowAllowed D r) :
    RowAllowed D (rows.foldr rowAdd (0,[])) := by
  induction rows with
  | nil => simp [RowAllowed]
  | cons r rows ih =>
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact h r (by simp) a ha
      · exact ih (fun s hs => h s (by simp [hs])) a ha

theorem foldRows_domain (rows : List Row) (ν : Nat → Nat)
    (h : ∀ r ∈ rows, RowDomain r ν) : RowDomain (rows.foldr rowAdd (0,[])) ν := by
  induction rows with
  | nil => simp [RowDomain]
  | cons r rows ih =>
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact h r (by simp) a ha
      · exact ih (fun s hs => h s (by simp [hs])) a ha

private theorem sum_doubled_identities {α : Type} (xs : List α)
    (f l e : α → Int) (H : Int)
    (h : ∀ a ∈ xs, 2*f a = l a*H+2*e a) :
    2*(xs.map f).sum = (xs.map l).sum*H+2*(xs.map e).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha := h a (by simp)
      have ht := ih (fun b hb => h b (by simp [hb]))
      simp only [List.map_cons,List.sum_cons]
      nlinarith only [ha,ht]

private theorem sum_single_identities {α : Type} (xs : List α)
    (f l e : α → Int) (H : Int)
    (h : ∀ a ∈ xs, f a = l a*H+e a) :
    (xs.map f).sum = (xs.map l).sum*H+(xs.map e).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha := h a (by simp)
      have ht := ih (fun b hb => h b (by simp [hb]))
      simp only [List.map_cons,List.sum_cons]
      nlinarith only [ha,ht]

/-- The ordinary-containing cancellation branch removes its entire actual
zero-leading class. Integer doubling cancels inside the proof; the runtime
replacement preserves the original undoubled row value. -/
theorem ordinaryClass_identity (D : Nat) (r : Row) (xs : List Item)
    (hD : RowAllowed D r) (hxs : ∀ a ∈ xs, a ∈ active (canonicalRow r))
    (ho : hasOrdinary xs = true) (hz : leading xs = 0)
    (ν : Nat → Nat) (ht : ∀ a ∈ xs, sourceTail a ≤ ν a.2.1)
    (H : Nat) (hH : ∀ a ∈ xs, wordValue (leader a).2 (ν a.2.1) = H) :
    RowAllowed D (classReplacement D xs) ∧ RowDomain (classReplacement D xs) ν ∧
      RowValue (classReplacement D xs) ν =
        (xs.map (fun a => a.1*(wordValue a.2.2 (ν a.2.1) : Int))).sum := by
  have hlocal := fun a ha => ordinaryResidual_identity D r a hD (hxs a ha) ν (ht a ha)
  have hadm : ∀ s ∈ xs.map ordinaryResidual, RowAllowed D s := by
    intro s hs
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
    exact (hlocal a ha).1
  have hdom : ∀ s ∈ xs.map ordinaryResidual, RowDomain s ν := by
    intro s hs
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
    exact (hlocal a ha).2.1
  simp only [classReplacement,ho,if_true]
  refine ⟨foldRows_allowed D _ hadm,foldRows_domain _ ν hdom,?_⟩
  have hsum := sum_doubled_identities xs
    (fun a => a.1*(wordValue a.2.2 (ν a.2.1) : Int))
    (fun a => a.1*(if isCounter a then 1 else 2))
    (fun a => RowValue (ordinaryResidual a) ν) (H : Int) (by
      intro a ha
      have heq := (hlocal a ha).2.2
      simpa only [show (leader a).1 = a.2.1 from rfl,hH a ha,mul_assoc] using heq)
  change (xs.map (fun a => a.1*(if isCounter a then 1 else 2))).sum = 0 at hz
  rw [hz,zero_mul] at hsum
  rw [foldRows_value,List.map_map]
  nlinarith only [hsum]

/-- The counter-only zero-leading class is cancelled against one actual
member attaining its minimum rank. The compiler stores only the minimum
rank; this proof witness does not alter the emitted syntax. -/
theorem counterClass_identity (D : Nat) (r : Row) (xs : List Item)
    (hD : RowAllowed D r) (hxs : ∀ a ∈ xs, a ∈ active (canonicalRow r))
    (ho : hasOrdinary xs = false) (hne : xs ≠ []) (hz : leading xs = 0)
    (ν : Nat → Nat) (ht : ∀ a ∈ xs, sourceTail a ≤ ν a.2.1)
    (hp : ∀ a ∈ xs, ∀ b ∈ xs,
      collisionTail a b ≤ ν a.2.1 ∧ collisionTail a b ≤ ν b.2.1)
    (hH : ∀ a ∈ xs, ∀ b ∈ xs,
      wordValue (leader a).2 (ν a.2.1) = wordValue (leader b).2 (ν b.2.1)) :
    RowAllowed D (classReplacement D xs) ∧ RowDomain (classReplacement D xs) ν ∧
      RowValue (classReplacement D xs) ν =
        (xs.map (fun a => a.1*(wordValue a.2.2 (ν a.2.1) : Int))).sum := by
  have hc := hasOrdinary_false xs ho
  have hbnd : ∀ a ∈ xs, rank a ≤ D :=
    fun a ha => current_rank_bound D r hD a (hxs a ha)
  obtain ⟨b,hb,hbrank⟩ := leastRank_attained D xs hne hbnd
  have hparB := counter_parameters D r b hD (hxs b hb) (hc b hb)
  have href : 3 ≤ leastRank D xs := by omega
  have hlocal : ∀ a ∈ xs,
      RowAllowed D (counterResidual (leastRank D xs) a) ∧
      RowDomain (counterResidual (leastRank D xs) a) ν := by
    intro a ha
    exact counterResidual_allowed_domain D r a hD (hxs a ha) (hc a ha)
      (leastRank D xs) href (leastRank_le_member D xs a ha) ν (ht a ha)
  have hadm : ∀ s ∈ xs.map (counterResidual (leastRank D xs)), RowAllowed D s := by
    intro s hs
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
    exact (hlocal a ha).1
  have hdom : ∀ s ∈ xs.map (counterResidual (leastRank D xs)), RowDomain s ν := by
    intro s hs
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
    exact (hlocal a ha).2
  simp only [classReplacement,ho,Bool.false_eq_true,if_false]
  refine ⟨foldRows_allowed D _ hadm,foldRows_domain _ ν hdom,?_⟩
  have hsum := sum_single_identities xs
    (fun a => a.1*(wordValue a.2.2 (ν a.2.1) : Int)) Prod.fst
    (fun a => RowValue (counterResidual (leastRank D xs) a) ν)
    (wordValue b.2.2 (ν b.2.1) : Int) (by
      intro a ha
      have heq := counterResidual_identity D r a b hD (hxs a ha) (hxs b hb)
        (hc a ha) (hc b hb) (by rw [hbrank]; exact leastRank_le_member D xs a ha) ν
        (ht a ha) (ht b hb) (hp a ha b hb).1 (hp a ha b hb).2 (hH a ha b hb)
      simpa only [hbrank] using heq)
  have hz' : (xs.map Prod.fst).sum = 0 := by
    have heq : leading xs = (xs.map Prod.fst).sum := by
      unfold leading
      congr 1
      apply List.map_congr_left
      intro a ha
      simp [hc a ha]
    rwa [heq] at hz
  rw [hz',zero_mul,zero_add] at hsum
  rw [foldRows_value,List.map_map]
  exact hsum.symm

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
