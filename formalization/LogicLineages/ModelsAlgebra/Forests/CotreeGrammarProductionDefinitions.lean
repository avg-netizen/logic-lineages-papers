module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRotationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarProduction
open CotreeGrammarOpen

/-- Occurrence of this exact typed subtree, not merely some node with its root label. -/
inductive Contains {Q : Type} {δ : Q → Q → Q} {q : Q} (u : Tree δ q) :
    {r : Q} → Tree δ r → Prop where
  | root : Contains u u
  | left {r s} {l : Tree δ r} {t : Tree δ s} : Contains u l → Contains u (.branch l t)
  | right {r s} {l : Tree δ r} {t : Tree δ s} : Contains u t → Contains u (.branch l t)

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarProduction
