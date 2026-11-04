module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticSchemasTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticSchemasProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticPredicateSubstitution PositiveArithmeticSchemas
open PositiveArithmeticOperatorsSupportProof SourceComputabilityFormulaSupportProof PositiveArithmeticPredicateSubstitutionProof

theorem allScalarTruth {α : Type} (phi : language.Formula (α ⊕ Fin 1)) (P : Nat → Prop) (v : α → Nat) :
    realize P (allOne phi) v ↔ ∀ x : Nat, realize P phi (Sum.elim v (fun _ => x)) := by
  rw [allOneTruth]
  constructor
  · intro h x
    exact h (fun _ => x)
  · intro h xs
    have he : xs = fun _ => xs 0 := by
      funext i
      exact congrArg xs (Subsingleton.elim i 0)
    rw [he]
    exact h (xs 0)

theorem predicateObjectTruth {α : Type} (P : Nat → Prop) (v : α → Nat) (x : Nat) :
    realize P (predicateAtObject (α := α)) (Sum.elim v (fun _ => x)) ↔ P x := by
  exact predicateTruth P (.var (.inr (0 : Fin 1))) (Sum.elim v (fun _ => x))

theorem replacementTruth {α : Type} (body : Positive (α ⊕ Fin 1))
    (theta : language.Formula (α ⊕ Fin 1)) (P : Nat → Prop) (v : α → Nat) (x : Nat) :
    realize P (substitutePredicate body (liftPredicateFormula theta)) (Sum.elim v (fun _ => x)) ↔
      realize (fun y => realize P theta (Sum.elim v (fun _ => y))) body.formula (Sum.elim v (fun _ => x)) := by
  rw [substitutionTruth]
  have he : (fun y => realize P (liftPredicateFormula theta)
      (Sum.elim (Sum.elim v (fun _ : Fin 1 => x)) (fun _ => y))) =
      (fun y => realize P theta (Sum.elim v (fun _ : Fin 1 => y))) := by
    funext y
    exact propext (actualLiftPredicateFormulaTruth α theta P v (fun _ => x) y)
  rw [he]

theorem actualClosureSchemaTruth : PositiveArithmeticSchemasTargets.ActualClosureSchemaTruth := by
  intro α body P v
  rw [closureSchema,allScalarTruth]
  apply forall_congr'
  intro x
  rw [generalImpTruth,predicateObjectTruth]

theorem actualLeastnessSchemaTruth : PositiveArithmeticSchemasTargets.ActualLeastnessSchemaTruth := by
  intro α body theta P v
  rw [leastnessSchema,generalImpTruth,allScalarTruth,allScalarTruth]
  apply imp_congr
  · apply forall_congr'
    intro x
    rw [generalImpTruth,replacementTruth]
  · apply forall_congr'
    intro x
    rw [generalImpTruth,predicateObjectTruth]

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticSchemasProof
