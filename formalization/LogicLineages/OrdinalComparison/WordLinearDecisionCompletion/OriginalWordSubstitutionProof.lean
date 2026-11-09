module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordValueProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluation.Proof
open PolynomialGraphCompletion

theorem rowSubstitution : Targets.RowSubstitution := by
  intro x n r ν
  rcases r with ⟨c, l⟩
  induction l with
  | nil => simp [specializeRow, RowValue]
  | cons a l ih =>
      by_cases h : a.2.1 = x
      <;> simp_all [specializeRow, RowValue, Function.update_apply, wordCorrect a.2.2 n]
      <;> omega

private theorem token_filter (x : Nat) (l : List (Int × Token)) :
    (l.filter (fun a => a.2.1 != x)).map Prod.snd =
      (l.map Prod.snd).filter (fun t => t.1 != x) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases h : a.2.1 = x <;> simp [h, ih]

theorem exactSupport : Targets.ExactSupport := by
  intro x n p
  induction p with
  | bot => rfl
  | top => rfl
  | atom a =>
      cases a with
      | nonnegative r =>
          simpa [specialize, specializeAtom, specializeRow, Formula.tokens,
            LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
            Atom.row] using token_filter x r.2
      | divisible m r =>
          simpa [specialize, specializeAtom, specializeRow, Formula.tokens,
            LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
            Atom.row] using token_filter x r.2
  | neg p ih => exact ih
  | conj p q ihp ihq =>
      simp only [specialize, Formula.tokens,
        LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
        List.flatMap_append, List.filter_append] at ihp ihq ⊢
      exact congrArg₂ List.append ihp ihq
  | disj p q ihp ihq =>
      simp only [specialize, Formula.tokens,
        LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit.Boolean.atoms,
        List.flatMap_append, List.filter_append] at ihp ihq ⊢
      exact congrArg₂ List.append ihp ihq

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluation.Proof
