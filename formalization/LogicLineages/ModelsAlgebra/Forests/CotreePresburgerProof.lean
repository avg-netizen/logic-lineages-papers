module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerTargets
public import Mathlib.Data.Fintype.BigOperators
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburger.Proof
open FirstOrder Language CotreeGrammarFlow CotreeGrammarRanks CotreeGrammarConnected

@[simp] theorem mem_elements {β : Type} [Fintype β] [LinearOrder β] (b : β) :
    b ∈ elements β := by simp [elements]

@[simp] theorem realize_allList {α β : Type} (xs : List β) (f : β → PFormula α)
    (v : α → Nat) : (allList xs f).Realize v ↔ ∀ x ∈ xs, (f x).Realize v := by
  induction xs with
  | nil => simp [allList]
  | cons x xs ih =>
    change (f x ⊓ allList xs f).Realize v ↔ _
    simp [ih]

@[simp] theorem realize_anyList {α β : Type} (xs : List β) (f : β → PFormula α)
    (v : α → Nat) : (anyList xs f).Realize v ↔ ∃ x ∈ xs, (f x).Realize v := by
  induction xs with
  | nil => simp [anyList]
  | cons x xs ih =>
    change (f x ⊔ anyList xs f).Realize v ↔ _
    simp [ih]

@[simp] theorem realize_allOf {α β : Type} [Fintype β] [LinearOrder β]
    (f : β → PFormula α) (v : α → Nat) :
    (allOf f).Realize v ↔ ∀ x, (f x).Realize v := by simp [allOf]

@[simp] theorem realize_anyOf {α β : Type} [Fintype β] [LinearOrder β]
    (f : β → PFormula α) (v : α → Nat) :
    (anyOf f).Realize v ↔ ∃ x, (f x).Realize v := by simp [anyOf]

@[simp] theorem realize_truth {α : Type} (p : Prop) [Decidable p] (v : α → Nat) :
    (truth p).Realize v ↔ p := by by_cases h : p <;> simp [truth, h]

@[simp] theorem realize_positive {α : Type} (t : PTerm α) (v : α → Nat) :
    (positive t).Realize v ↔ 0 < t.realize v := by
  simp [positive, Nat.pos_iff_ne_zero]

@[simp] theorem realize_ite {α : Type} (p : Prop) [Decidable p]
    (s t : PTerm α) (v : α → Nat) :
    (if p then s else t).realize v = if p then s.realize v else t.realize v := by
  split <;> rfl

@[simp] theorem realize_listSum {α : Type} (ts : List (PTerm α)) (v : α → Nat) :
    ts.sum.realize v = (ts.map (Term.realize v)).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih]

@[simp] theorem realize_sumAll {α β : Type} [Fintype β] [LinearOrder β]
    (f : β → PTerm α) (v : α → Nat) :
    (sumAll f).realize v = ∑ x, (f x).realize v := by
  rw [sumAll, realize_listSum, List.map_map, elements]
  rw [← List.sum_toFinset _ (Finset.sort_nodup _ _)]
  simp [elements]

@[simp] theorem realize_existsOf {α β : Type} [Fintype β] [LinearOrder β]
    (φ : PFormula (α ⊕ β)) (v : α → Nat) :
    (existsOf φ).Realize v ↔ ∃ w : β → Nat, φ.Realize (Sum.elim v w) := by
  let e := (Fintype.orderIsoFinOfCardEq β rfl).toEquiv.symm
  rw [existsOf]
  simp only [Nat.add_zero, BoundedFormula.realize_exs, BoundedFormula.realize_relabel,
    Function.comp_def, Fin.castAdd_zero, Sum.elim_map, id_eq]
  refine Equiv.exists_congr ?_ ?_
  · exact ⟨fun w => w ∘ e, fun w => w ∘ e.symm,
      fun _ => by simp [Function.comp_def], fun _ => by simp [Function.comp_def]⟩
  · intro x
    rw [Formula.Realize, iff_eq_eq]
    congr
    funext i
    exact i.elim0

section Finite
variable {Q : Type} [Fintype Q] [LinearOrder Q]
variable (counts : Finset Q → Nat) (v : Witness Q → Nat)

@[simp] theorem realize_binaryTerm (r s : Q) :
    (binaryTerm r s).realize (Sum.elim counts v) = (decodeCounts v).binary (r,s) := rfl
@[simp] theorem realize_terminalTerm (B : Finset Q) (q : Q) :
    (terminalTerm B q).realize (Sum.elim counts v) = (decodeCounts v).terminal (B,q) := rfl
@[simp] theorem realize_rankTerm (q : Q) :
    (rankTerm q).realize (Sum.elim counts v) = decodeRank v q := rfl

@[simp] theorem realize_terminalTotalTerm (B : Finset Q) :
    (terminalTotalTerm B).realize (Sum.elim counts v) = terminalTotal (decodeCounts v) B := by
  simp [terminalTotalTerm, terminalTotal]

@[simp] theorem realize_consumedTerm (δ : Q → Q → Q) (q : Q) :
    (consumedTerm δ q).realize (Sum.elim counts v) = consumed δ (decodeCounts v) q := by
  simp [consumedTerm, consumed, Fintype.sum_prod_type]
  exact Equiv.sum_comp ofColex (fun B => (decodeCounts v).terminal (B,q))

@[simp] theorem realize_producedTerm (q : Q) :
    (producedTerm q).realize (Sum.elim counts v) = produced (decodeCounts v) q := by
  simp [producedTerm, produced, Fintype.sum_prod_type, Nat.mul_add, mul_ite]

@[simp] theorem realize_edgeFormula (δ : Q → Q → Q) (p q : Q) :
    (edgeFormula δ p q).Realize (Sum.elim counts v) ↔ UsedEdge δ (decodeCounts v) p q := by
  simp [edgeFormula, UsedEdge, and_assoc]

@[simp] theorem realize_ranksFormula (δ : Q → Q → Q) (root : Q) :
    (ranksFormula δ root).Realize (Sum.elim counts v) ↔
      RankedSupport δ root (decodeCounts v) (decodeRank v) := by
  simp [ranksFormula, RankedSupport, and_assoc]

theorem realize_matrix (δ : Q → Q → Q) (root : Q) :
    (flowFormula δ root ⊓ ranksFormula δ root).Realize (Sum.elim counts v) ↔
      Constraints δ root counts (decodeCounts v) (decodeRank v) := by
  simp [flowFormula, Constraints, and_assoc]

/-- A concrete valuation realizes every production-count and rank assignment. -/
def encodeWitness (c : Counts Q) (rank : Q → Nat) (w : Witness Q) : Nat :=
  match ofLex w with
  | .inl p => c.binary (ofLex p)
  | .inr w => match ofLex w with
    | .inl p => c.terminal (ofColex (ofLex p).1, (ofLex p).2)
    | .inr q => rank q

@[simp] theorem decode_encode_counts (c : Counts Q) (rank : Q → Nat) :
    decodeCounts (encodeWitness c rank) = c := by cases c; rfl
@[simp] theorem decode_encode_rank (c : Counts Q) (rank : Q → Nat) :
    decodeRank (encodeWitness c rank) = rank := rfl
end Finite

theorem formulaExact : Targets.FormulaExact := by
  intro Q _ _ δ root counts
  rw [formula, realize_existsOf]
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨decodeCounts v, decodeRank v, (realize_matrix counts v δ root).mp hv⟩
  · rintro ⟨c,rank,h⟩
    refine ⟨encodeWitness c rank, ?_⟩
    rw [realize_matrix]
    simpa using h

end LogicLineages.ModelsAlgebra.Forests.CotreePresburger.Proof
