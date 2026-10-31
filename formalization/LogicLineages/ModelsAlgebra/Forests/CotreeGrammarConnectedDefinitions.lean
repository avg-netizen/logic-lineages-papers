module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlowStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarConnected
open CotreeGrammarFlow

def UsedEdge {Q : Type} (δ : Q → Q → Q) (c : Counts Q) (x y : Q) : Prop :=
  ∃ r s, 0 < c.binary (r,s) ∧ δ r s = x ∧ (r = y ∨ s = y)

/-- Every used nonterminal lies in the positive-production support reachable
from the actual root. This excludes disconnected circulation witnesses. -/
def Connected {Q : Type} [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q)
    (root : Q) (c : Counts Q) : Prop :=
  ∀ q, 0 < consumed δ c q → Relation.ReflTransGen (UsedEdge δ c) root q

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarConnected
