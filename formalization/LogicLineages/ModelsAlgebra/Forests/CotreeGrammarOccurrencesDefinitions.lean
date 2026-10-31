module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarShapeStatementChecks
public import Mathlib.Data.List.FinRange
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOccurrences
open ForestParseRepresentationBinary

/-- Same binary skeleton with a relation on each corresponding leaf occurrence. -/
inductive Paired {I J : Type} (R : I → J → Prop) : Shape I → Shape J → Prop where
  | leaf {i j} : R i j → Paired R (.leaf i) (.leaf j)
  | node {p q r s} : Paired R p r → Paired R q s → Paired R (.node p q) (.node r s)

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOccurrences
