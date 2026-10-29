module

public import LogicLineages.ComputabilityKnowledge.PositiveExpressionProperties
public import LogicLineages.ComputabilityKnowledge.PredictionGame
public import LogicLineages.ComputabilityKnowledge.GorbowSubstitution
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

/-- Evaluation in the fixed source grammar is positive on its actual domain. -/
theorem positive_expression_evaluation {ι : Type} :
    ∀ (ρ : ι → PositiveExpression.PosNat) (e : PositiveExpression.Expr ι),
      0 < e.eval ρ :=
  PositiveExpressionProperties.eval_positive

/-- The source-system compiler has the depth bound claimed in paper02. -/
theorem exponential_collision_depth {ι : Type}
    (equations : List (PositiveExpression.Expr ι × PositiveExpression.Expr ι))
    (h : ∀ pair ∈ equations, pair.1.depth ≤ 1 ∧ pair.2.depth ≤ 1) :
    (Comparators.ExponentialGap.systemLeft equations).depth ≤ 2 ∧
      (Comparators.ExponentialGap.systemRight equations).depth ≤ 2 :=
  PositiveExpressionProperties.system_depth equations h

/-- The concrete simultaneous-history diagonal, with no computability claim. -/
theorem semantic_prediction_obstruction :
    ∀ predictor : PredictionGame.Policy,
      ¬ PredictionGame.Learns predictor (PredictionGame.antiEvader predictor) :=
  PredictionGame.anti_not_learned

/-- Simultaneous substitution has the actual source-term interpretation. -/
theorem gorbow_term_substitution {m n : Nat}
    (I : GorbowSyntax.Interpretation) (v : Fin n → Nat)
    (σ : Fin m → GorbowSyntax.Term n) (t : GorbowSyntax.Term m) :
    (GorbowSubstitution.substitute σ t).realize I v =
      t.realize I (fun i => (σ i).realize I v) :=
  GorbowSubstitution.substitute_realize I v σ t

/-- Actual falsity of the represented closed arithmetic contradiction. -/
theorem gorbow_false_equality :
    ∀ I : GorbowSyntax.Interpretation,
      ¬ GorbowSyntax.falseEquality.realize I Fin.elim0 :=
  GorbowSyntax.falseEquality_not_realized

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
