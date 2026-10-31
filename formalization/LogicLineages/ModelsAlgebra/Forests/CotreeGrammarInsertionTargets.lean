module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarProductionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInsertion.Targets
open CotreeGrammarOpen CotreeGrammarRotation CotreeGrammarFlow

/-- Splice a genuine one-hole cycle at an actual expanded or unexpanded node. -/
def CycleInsertOccurrence : Prop := ∀ (Q : Type) [DecidableEq Q] (δ : Q → Q → Q)
  x z (t : Tree δ x) (u : Tree δ z), holes t = [x] → Occurs x u →
  ∃ v : Tree δ z, counts v = addCounts (counts u) (counts t) ∧ (holes v).Perm (holes u)

/-- Direct cycle insertion at the indicated child of a positive actual production,
with exact production counts and every remaining open occurrence preserved. -/
def CycleInsertProduction : Prop := ∀ (Q : Type) [DecidableEq Q] (δ : Q → Q → Q)
  x z (t : Tree δ x) (u : Tree δ z) r s,
  holes t = [x] → 0 < (counts u).binary (r,s) → (r = x ∨ s = x) →
  ∃ v : Tree δ z, counts v = addCounts (counts u) (counts t) ∧ (holes v).Perm (holes u)

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarInsertion.Targets
