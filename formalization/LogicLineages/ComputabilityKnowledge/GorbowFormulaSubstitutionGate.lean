module

public import LogicLineages.ComputabilityKnowledge.GorbowFormulaSubstitution
public meta import LogicLineages.Audit

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.StatementChecks

theorem gorbow_formula_substitution {m n : Nat}
    (φ : GorbowSyntax.Formula m) (I : GorbowSyntax.Interpretation)
    (v : Fin n → Nat) (σ : Fin m → GorbowSyntax.Term n) :
    (GorbowFormulaSubstitution.substituteFormula σ φ).realize I v ↔
      φ.realize I (fun i => (σ i).realize I v) :=
  GorbowFormulaSubstitution.substituteFormula_realize φ I v σ

end LogicLineages.ComputabilityKnowledge.StatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge
