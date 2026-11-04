module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TaggedArithmeticOperatorsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.TaggedArithmeticOperatorsSupportProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms TaggedArithmeticOperators
open PositiveArithmeticOperatorsSupportProof PositiveArithmeticTransformsProof

theorem tagInjective (odd : Bool) : Function.Injective (tagNumber odd) := by
  intro x y h
  cases odd <;> simp [tagNumber] at h <;> omega

theorem tagsDisjoint (x y : Nat) : tagNumber false x ≠ tagNumber true y := by
  simp [tagNumber]
  omega

theorem branchTruth (odd : Bool) (body : Positive (Fin 2)) (P : Nat → Prop) (context z : Nat) :
    realize P (taggedBranch odd body).formula ![context,z] ↔
      ∀ x : Nat, z=tagNumber odd x → realize (fun y => P (tagNumber odd y)) body.formula ![context,x] := by
  rw [taggedBranch,allTruth]
  have hv (xs : Fin 1 → Nat) :
      (Sum.elim ![context,z] xs) ∘ ![Sum.inl (0 : Fin 2),Sum.inr (0 : Fin 1)] = ![context,xs 0] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  have hrel (xs : Fin 1 → Nat) := positiveRelabelTruth (Fin 2) (Fin 2 ⊕ Fin 1)
    ![Sum.inl (0 : Fin 2),Sum.inr (0 : Fin 1)] (tagPredicate odd body) P (Sum.elim ![context,z] xs)
  have htag (v : Fin 2 → Nat) := positiveTagTruth (Fin 2) odd body P v
  simp only [guardedTruth,hrel,htag,Formula.realize_equal,
    tagTermTruth,Term.realize_var,Sum.elim_inl,Sum.elim_inr,Matrix.cons_val_one,Matrix.cons_val_zero,hv]
  constructor
  · intro h x hx
    exact h (fun _ => x) hx
  · intro h xs hx
    exact h (xs 0) hx

theorem sameBranch (odd : Bool) (body : Positive (Fin 2)) (P : Nat → Prop) (context x : Nat) :
    realize P (taggedBranch odd body).formula ![context,tagNumber odd x] ↔
      realize (fun y => P (tagNumber odd y)) body.formula ![context,x] := by
  rw [branchTruth]
  constructor
  · intro h
    exact h x rfl
  · intro h y he
    have hy := tagInjective odd he
    subst y
    exact h

end LogicLineages.OrdinalComparison.TerminationOrdering.TaggedArithmeticOperatorsSupportProof
