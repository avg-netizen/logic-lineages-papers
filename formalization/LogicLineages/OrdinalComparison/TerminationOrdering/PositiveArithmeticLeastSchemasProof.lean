module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSchemasTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSchemasProof
open PositiveArithmeticOperators PositiveArithmeticLeastSet PositiveArithmeticSchemas PositiveArithmeticLeastSchemas

theorem actualParameterizedBodyTruth : PositiveArithmeticLeastSchemasTargets.ActualParameterizedBodyTruth := by
  intro body P context x
  unfold parameterizedBody
  rw [PositiveArithmeticTransformsProof.relabelTruth]
  have he : (Sum.elim ![context] (fun _ : Fin 1 => x)) ∘ ![Sum.inl 0,Sum.inr 0] = ![context,x] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  rw [he]

theorem actualLeastClosureSchema : PositiveArithmeticLeastSchemasTargets.ActualLeastClosureSchema := by
  intro body context
  apply (PositiveArithmeticSchemasProof.actualClosureSchemaTruth (Fin 1) (parameterizedBody body)
    (fun x => x ∈ leastSet body context) ![context]).mpr
  intro x hx
  exact (PositiveArithmeticLeastSetProof.semanticLeastUnfolding body context x).mpr
    ((actualParameterizedBodyTruth body _ context x).mp hx)

theorem actualLeastLeastnessSchema : PositiveArithmeticLeastSchemasTargets.ActualLeastLeastnessSchema := by
  intro body context theta
  apply (PositiveArithmeticSchemasProof.actualLeastnessSchemaTruth (Fin 1) (parameterizedBody body) theta
    (fun x => x ∈ leastSet body context) ![context]).mpr
  intro h
  let A : Set Nat := {x | realize (fun y => y ∈ leastSet body context) theta (Sum.elim ![context] (fun _ => x))}
  have hclosed : ∀ x, realize (fun y => y ∈ A) body.formula ![context,x] → x ∈ A := by
    intro x hx
    exact h x ((actualParameterizedBodyTruth body (fun y => y ∈ A) context x).mpr hx)
  exact PositiveArithmeticLeastSetProof.semanticLeastness body context A hclosed

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticLeastSchemasProof
