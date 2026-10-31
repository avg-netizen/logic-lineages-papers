module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarReconstructDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarReconstruct.Targets
open CotreeGrammarOpen CotreeGrammarFlow CotreeGrammarForest CotreeGrammarRanks CotreeGrammarConnected

def ForestReconstruction : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) root w
    (F : List (Packed δ)) (rank : Q → Nat),
    Realizes δ root w (forestCounts F) → RankedSupport δ root (forestCounts F) rank →
    ∃ t : Tree δ root, holes t = [] ∧ counts t = forestCounts F

/-- Reconstruction preserves full requested terminal multiplicities; it does
not falsely prescribe the order of the reconstructed derivation's terminal word. -/
def WordReconstruction : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) root w (F : List (Packed δ)),
    Realizes δ root w (forestCounts F) → Connected δ root (forestCounts F) →
    ∃ v, CotreeGrammar.Builds δ root v ∧ v.Perm w

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarReconstruct.Targets
