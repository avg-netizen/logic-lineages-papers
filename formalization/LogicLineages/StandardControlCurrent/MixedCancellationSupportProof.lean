module
public import LogicLineages.StandardControlCurrent.MixedCancellationDefinitions
public import LogicLineages.StandardControlCurrent.MixedCancellationTargets
@[expose] public section
namespace LogicLineages.StandardControlCurrent.MixedCancellation
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm

private theorem part_support (r : Row) (j : Nat) :
    (j ∈ (positiveTerm r).variables ↔ ∃ a ∈ r.2, j ∈ a.2.term.variables) ∧
    (j ∈ (negativeTerm r).variables ↔ ∃ a ∈ r.2, j ∈ a.2.term.variables) := by
  have hf (f : Int → Nat) (xs : List (Int × Summand)) :
      j ∈ (xs.foldr (fun a rest => Term.add (.multiply (f a.1) a.2.term) rest) (.numeral 0)).variables ↔
        ∃ a ∈ xs, j ∈ a.2.term.variables := by
    induction xs with
    | nil => simp [Term.variables]
    | cons a xs ih => simp [Term.variables,ih]
  constructor
  · simpa only [positiveTerm,Term.variables,List.nil_append] using hf Int.toNat r.2
  · simpa only [negativeTerm,Term.variables,List.nil_append] using hf (fun z => (-z).toNat) r.2

private theorem atom_support (a : Atom) (j : Nat) :
    j ∈ a.compile.variables ↔ ∃ b ∈ a.row.2, j ∈ b.2.term.variables := by
  cases a <;> simp [Atom.compile,Atom.row,atMost,absoluteTerm,Matrix.variables,Term.variables,
    (part_support _ j).1,(part_support _ j).2]

private theorem retained_member (r : Row) (bs : List Bool) (a : Int × Summand)
    (h : a ∈ (retained r bs).2) : a ∈ r.2 := by
  obtain ⟨x,hx,he⟩ := List.mem_filterMap.mp h
  have ha : x.1=a := by
    split at he <;> simp_all
  rw [← ha]
  exact (List.of_mem_zip hx).1

private theorem context_support (c : Context) (p q : Matrix)
    (h : ∀ j, j ∈ p.variables → j ∈ q.variables) :
    ∀ j, j ∈ (c.plug p).variables → j ∈ (c.plug q).variables := by
  induction c with
  | hole => exact h
  | neg c ih => exact ih
  | conjLeft c r ih => intro j hj; exact List.mem_append.mpr ((List.mem_append.mp hj).imp (ih j) id)
  | conjRight r c ih => intro j hj; exact List.mem_append.mpr ((List.mem_append.mp hj).imp id (ih j))
  | disjLeft c r ih => intro j hj; exact List.mem_append.mpr ((List.mem_append.mp hj).imp (ih j) id)
  | disjRight r c ih => intro j hj; exact List.mem_append.mpr ((List.mem_append.mp hj).imp id (ih j))

theorem support : MixedCancellationTargets.Support := by
  intro c a bs j hj
  by_cases he : enabled a.row bs=true
  · have ha : ∀ k, k ∈ (replaceRow a (retained a.row bs)).compile.variables → k ∈ a.compile.variables := by
      intro k hk
      obtain ⟨b,hb,hk⟩ := (atom_support _ k).mp hk
      have hr : (replaceRow a (retained a.row bs)).row = retained a.row bs := by cases a <;> rfl
      rw [hr] at hb
      exact (atom_support _ k).mpr ⟨b,retained_member _ _ _ hb,hk⟩
    have hh : ∀ k, k ∈ (Matrix.conjunction (domainFormula a.row).compile
        (replaceRow a (retained a.row bs)).compile).variables → k ∈ (guardedAtom a).compile.variables := by
      intro k hk
      exact List.mem_append.mpr ((List.mem_append.mp hk).imp id (ha k))
    have hc := context_support c _ _ hh
    simp only [step,he,if_true,rewritten,before,Matrix.variables] at hj ⊢
    exact List.mem_append.mpr ((List.mem_append.mp hj).imp id (hc j))
  · simpa [step,he] using hj
end LogicLineages.StandardControlCurrent.MixedCancellation
