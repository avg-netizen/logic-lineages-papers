module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationBinaryDefinitions
public import LogicLineages.ModelsAlgebra.Forests.ProfileAutomatonEncodingDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarShape
open ForestParseRepresentationBinary

def word {I : Type} : Shape I → List I
  | .leaf i => [i]
  | .node p q => word p ++ word q

def fold {I Q : Type} (δ : Q → Q → Q) (v : I → Q) : Shape I → Q
  | .leaf i => v i
  | .node p q => δ (fold δ v p) (fold δ v q)

/-- Each position selects a state from its entire child-state subset. -/
def Valid {Q : Type} (s : Shape (Finset Q × Q)) : Prop :=
  ∀ p : Positions s, (label s p).2 ∈ (label s p).1

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarShape
