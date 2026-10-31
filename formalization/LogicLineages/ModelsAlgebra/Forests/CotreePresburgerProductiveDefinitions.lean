module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductDefinitions
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCountVectorDefinitions
public import Mathlib.Data.Finset.Lattice.Fold
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductive
open RankedParse ForestParseRepresentationCotree CotreePresburgerBoolean

def height : Cotree → Nat
  | .atom => 1
  | .node _ _ c => (Finset.univ.sup (fun i => height (c i))) + 1

/-- The actual existential Presburger count-vector query from the source.
No arithmetic satisfiability solver is assumed or implemented here. -/
def Enabled {Q : Type} [Fintype Q] [DecidableEq Q] (A : Automaton Q) (R : Finset Q) (q : Q) : Prop :=
  ∃ o, ∃ counts : Q → Nat, (A.node o q).Realize counts ∧ 2 ≤ ∑ s, counts s ∧
    ∀ s, s ∉ R → counts s = 0

/-- Semantic finite iteration, deliberately noncomputable until the actual
Presburger satisfiability procedure is supplied. -/
noncomputable def step {Q : Type} [Fintype Q] [DecidableEq Q] (A : Automaton Q) (R : Finset Q) : Finset Q := by
  classical
  exact R ∪ {A.leaf} ∪ Finset.univ.filter (Enabled A R)

noncomputable def reachable {Q : Type} [Fintype Q] [DecidableEq Q] (A : Automaton Q) : Nat → Finset Q
  | 0 => ∅
  | n+1 => step A (reachable A n)

noncomputable def productive {Q : Type} [Fintype Q] [DecidableEq Q] (A : Automaton Q) : Finset Q :=
  reachable A (Fintype.card Q)

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductive
