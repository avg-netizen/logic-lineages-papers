module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticPredicateSubstitutionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticPredicateSubstitutionProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticPredicateSubstitution
open PositiveArithmeticOperatorsSupportProof SourceComputabilityFormulaSupportProof

theorem actualLiftPredicateFormulaTruth : PositiveArithmeticPredicateSubstitutionTargets.ActualLiftPredicateFormulaTruth := by
  intro α theta Q v xs x
  rw [liftPredicateFormula,generalRelabelTruth]
  have he : (Sum.elim (Sum.elim v xs) (fun _ : Fin 1 => x)) ∘
      Sum.map (Sum.inl : α → α ⊕ Fin 1) id = Sum.elim v (fun _ : Fin 1 => x) := by
    funext i
    cases i <;> rfl
  rw [he]

theorem generalSubstitutionTruth {α β : Type} (theta : language.Formula α) (terms : α → language.Term β)
    (Q : Nat → Prop) (v : β → Nat) :
    realize Q (theta.subst terms) v ↔
      letI := naturalStructure Q
      realize Q theta (fun i => (terms i).realize v) := by
  letI := naturalStructure Q
  simp only [realize,Formula.Realize,BoundedFormula.realize_subst]

theorem atomSubstitutionTruth {α : Type} (theta : language.Formula (α ⊕ Fin 1))
    (t : OrdinaryArithmetic.Term α) (Q : Nat → Prop) (v : α → Nat) :
    realize Q (theta.subst (Sum.elim Term.var (fun _ => arithmeticEmbedding.onTerm t))) v ↔
      realize Q theta (Sum.elim v (fun _ => t.realize v)) := by
  rw [generalSubstitutionTruth]
  letI := naturalStructure Q
  letI := expansion Q
  have he : (fun i : α ⊕ Fin 1 => ((Sum.elim Term.var (fun _ : Fin 1 => arithmeticEmbedding.onTerm t)) i).realize v) =
      Sum.elim v (fun _ : Fin 1 => t.realize v) := by
    funext i
    cases i with
    | inl a => rfl
    | inr a => exact arithmeticEmbedding.realize_onTerm t v
  rw [he]

theorem substitutionTruth {α : Type} (body : Positive α) :
    ∀ (theta : language.Formula (α ⊕ Fin 1)) (Q : Nat → Prop) (v : α → Nat),
    realize Q (substitutePredicate body theta) v ↔
      realize (fun x => realize Q theta (Sum.elim v (fun _ => x))) body.formula v := by
  induction body with
  | arithmetic phi =>
    intro theta Q v
    change realize Q (arithmeticEmbedding.onFormula phi) v ↔ realize _ (arithmeticEmbedding.onFormula phi) v
    rw [embeddingTruth,embeddingTruth]
  | predicate t =>
    intro theta Q v
    change realize Q (theta.subst _) v ↔ realize _ (Positive.predicate t).formula v
    rw [predicateTruth]
    exact atomSubstitutionTruth theta t Q v
  | conj p q ihp ihq =>
    intro theta Q v
    change realize Q (substitutePredicate p theta ⊓ substitutePredicate q theta) v ↔ realize _ (Positive.conj p q).formula v
    rw [generalConjTruth,conjTruth,ihp,ihq]
  | guarded guard p ih =>
    intro theta Q v
    change realize Q ((arithmeticEmbedding.onFormula guard).imp (substitutePredicate p theta)) v ↔ realize _ (Positive.guarded guard p).formula v
    rw [generalImpTruth,embeddingTruth,guardedTruth,ih]
  | all p ih =>
    intro theta Q v
    change realize Q (allOne (substitutePredicate p (liftPredicateFormula theta))) v ↔ realize _ (Positive.all p).formula v
    rw [allOneTruth,allTruth]
    apply forall_congr'
    intro xs
    rw [ih]
    have he : (fun x => realize Q (liftPredicateFormula theta) (Sum.elim (Sum.elim v xs) (fun _ => x))) =
        (fun x => realize Q theta (Sum.elim v (fun _ => x))) := by
      funext x
      exact propext (actualLiftPredicateFormulaTruth _ theta Q v xs x)
    rw [he]

theorem actualPredicateSubstitutionTruth : PositiveArithmeticPredicateSubstitutionTargets.ActualPredicateSubstitutionTruth := by
  intro α body theta Q v
  exact substitutionTruth body theta Q v

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticPredicateSubstitutionProof
