module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarNormalDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarNormal.Targets
open CotreeGrammarFlow CotreeGrammarOpen CotreeGrammarForest

def RealizedBalance : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) root w (F : List (Packed δ)),
    Realizes δ root w (forestCounts F) → Balanced root F

/-- Maximal cross-tree gluing leaves exactly one closed root tree and
pairwise-distinct non-root single-hole cycles. Bare-hole elimination is separate. -/
def NormalStructure : Prop :=
  ∀ (Q : Type) [DecidableEq Q] (δ : Q → Q → Q) root (F : List (Packed δ)),
    Balanced root F → NoCrossHole F →
    ∃ t : Tree δ root, ∃ rest : List (Packed δ),
      F.Perm (⟨root,t⟩ :: rest) ∧ holes t = [] ∧
      (∀ u ∈ rest, u.1 ≠ root ∧ holes u.2 = [u.1]) ∧ (roots F).Nodup

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarNormal.Targets
