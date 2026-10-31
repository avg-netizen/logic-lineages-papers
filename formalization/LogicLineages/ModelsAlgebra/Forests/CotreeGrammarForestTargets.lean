module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarForestDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarForest.Targets
open CotreeGrammarFlow

def ForestBalance : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) (F : List (Packed δ)) q,
    consumed δ (forestCounts F) q + (forestHoles F).count q =
      (roots F).count q + produced (forestCounts F) q

def ForestTerminals : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) (F : List (Packed δ)) B,
    terminalTotal (forestCounts F) B = (forestWord F).count B

/-- Actual zipper gluing yields a finite forest with the same production
multiplicities and no remaining cross-tree root/hole match. -/
def NormalForestExists : Prop :=
  ∀ (Q : Type) [DecidableEq Q] (δ : Q → Q → Q) (F : List (Packed δ)),
    ∃ G : List (Packed δ), forestCounts G = forestCounts F ∧ NoCrossHole G ∧ NoBareHole G

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarForest.Targets
