module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerGrammarStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCounts
open CotreePresburger

/-- An executable canonical word with the given finite terminal-count vector.
This symbolic list construction is not numerically evaluated in the proof. -/
def wordOfCounts {Q : Type} [Fintype Q] [LinearOrder Q]
    (counts : Finset Q → Nat) : List (Finset Q) :=
  (elements (Colex (Finset Q))).flatMap (fun B => List.replicate (counts (ofColex B)) (ofColex B))

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCounts
