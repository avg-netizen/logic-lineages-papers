module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarForestStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInitialForest
open CotreeGrammarFlow CotreeGrammarOpen CotreeGrammarForest

/-- Every listed component contains exactly one literal grammar production.
Finite enumeration here is symbolic; no large state space is evaluated. -/
noncomputable def initialForest {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Q → Q) (c : Counts Q) : List (Packed δ) :=
  (Finset.univ.toList.flatMap (fun p : Q × Q =>
    List.replicate (c.binary p) ⟨δ p.1 p.2, .branch (.hole p.1) (.hole p.2)⟩)) ++
  (Finset.univ.toList.flatMap (fun p : Finset Q × Q =>
    if h : p.2 ∈ p.1 then List.replicate (c.terminal p) ⟨p.2, .terminal p.1 p.2 h⟩ else []))

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInitialForest
