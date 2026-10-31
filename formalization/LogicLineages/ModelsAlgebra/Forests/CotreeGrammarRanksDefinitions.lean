module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarConnectedStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRanks
open CotreeGrammarFlow CotreeGrammarConnected

/-- Finite predecessor-rank constraints for positive production support.
Root rank is one. Other unused states have rank zero. Each other used state
has a positive predecessor whose rank is exactly one less. -/
def RankedSupport {Q : Type} [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q)
    (root : Q) (c : Counts Q) (rank : Q → Nat) : Prop :=
  rank root = 1 ∧ ∀ q, q ≠ root →
    ((consumed δ c q = 0 ∧ rank q = 0) ∨
      (0 < consumed δ c q ∧ ∃ p, 0 < rank p ∧ rank q = rank p + 1 ∧ UsedEdge δ c p q))

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRanks
