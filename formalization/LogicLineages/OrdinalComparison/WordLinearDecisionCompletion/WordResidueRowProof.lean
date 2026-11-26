module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidueWordProof
public import Mathlib.Tactic.Ring

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidue.Proof
open PolynomialGraphCompletion

theorem mappedSumBound {α : Type*} (f : α → Nat) (xs : List α)
    (a : α) (ha : a ∈ xs) : f a ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · simp
      · have h := ih ha
        simp only [List.map_cons, List.sum_cons]
        omega

theorem mappedSumResidue {α : Type*} (m : Int) (f g : α → Int) (xs : List α)
    (h : ∀ a ∈ xs, Int.ModEq m (f a) (g a)) :
    Int.ModEq m (xs.map f).sum (xs.map g).sum := by
  induction xs with
  | nil => exact Int.ModEq.refl 0
  | cons a xs ih =>
      exact (h a List.mem_cons_self).add
        (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem rowAffineValue (m : Nat) (r : Row) (ν : Nat → Nat) :
    RowValue (row m r) ν = r.1 +
      (r.2.map (fun a => a.1 * ((affine m a.2.2).1 * (ν a.2.1 : Int) +
        (affine m a.2.2).2))).sum := by
  unfold RowValue row
  simp only [List.map_map, Function.comp_def, wordValue]
  have h : ∀ xs : List (Int × (Nat × Word)),
      (xs.map (fun a => a.1 * (affine m a.2.2).2)).sum +
        (xs.map (fun a => (a.1 * (affine m a.2.2).1) * (ν a.2.1 : Int))).sum =
      (xs.map (fun a => a.1 * ((affine m a.2.2).1 * (ν a.2.1 : Int) +
        (affine m a.2.2).2))).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons a xs ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [show a.1 * (affine m a.2.2).2 +
            (xs.map (fun b => b.1 * (affine m b.2.2).2)).sum +
            ((a.1 * (affine m a.2.2).1) * (ν a.2.1 : Int) +
              (xs.map (fun b => (b.1 * (affine m b.2.2).1) * (ν b.2.1 : Int))).sum) =
          a.1 * ((affine m a.2.2).1 * (ν a.2.1 : Int) + (affine m a.2.2).2) +
            ((xs.map (fun b => b.1 * (affine m b.2.2).2)).sum +
              (xs.map (fun b => (b.1 * (affine m b.2.2).1) * (ν b.2.1 : Int))).sum) by ring]
        rw [ih]
  rw [add_assoc, h]

theorem actualRowResidue : Targets.ActualRowResidue := by
  intro D m hm r hr ν ht
  have hw : ∀ a ∈ r.2, WordDomain a.2.2 (ν a.2.1) ∧
      Int.ModEq (m : Int) (wordValue a.2.2 (ν a.2.1) : Int)
        ((affine m a.2.2).1 * (ν a.2.1 : Int) + (affine m a.2.2).2) := by
    intro a ha
    apply literalWordResidue D m hm a.2.2 (hr a ha) (ν a.2.1)
    exact (mappedSumBound (fun b : Int × (Nat × Word) => tail m b.2.2) r.2 a ha).trans
      (ht a.2.1 (List.mem_map.mpr ⟨a, ha, rfl⟩))
  refine ⟨fun a ha => (hw a ha).1, ?_⟩
  rw [rowAffineValue]
  exact (mappedSumResidue (m : Int) _ _ r.2
    (fun a ha => (hw a ha).2.mul_left a.1)).add_left r.1

theorem actualDivisibility : Targets.ActualDivisibility := by
  intro D m r hr ν ht
  have h := (actualRowResidue D (m+1) (by omega) r hr ν ht).2
  rw [← Int.modEq_zero_iff_dvd, ← Int.modEq_zero_iff_dvd]
  exact ⟨fun hx => h.symm.trans hx, fun hx => h.trans hx⟩

theorem literalRawSyntax : Targets.LiteralRawSyntax := by
  intro m r
  refine ⟨rfl, ?_⟩
  intro a ha
  rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
  rfl

theorem exactNames : Targets.ExactNames := by
  intro m r
  simp only [rowVariables, row, List.map_map, Function.comp_def]

theorem outputDomainsAndDegree : Targets.OutputDomainsAndDegree := by
  intro D m r ν
  constructor
  · intro a ha
    rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
    trivial
  · intro a ha
    rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
    intro letter hletter
    simp at hletter

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidue.Proof
