module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductiveDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductive.Targets
open RankedParse ProfileAutomatonEncoding ForestParseRepresentationCotree
open CotreePresburgerBoolean CotreePresburgerProduct CotreePresburgerPullback

def EnabledListExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (A : Automaton Q) (R : Finset Q) q,
    Enabled A R q ↔ ∃ o, ∃ n, ∃ v : Fin (n+2) → Q,
      (∀ i, v i ∈ R) ∧ (A.node o q).Realize (wordCounts (List.ofFn v))

def ReachableHeightExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (A : Automaton Q) n q,
    q ∈ reachable A n ↔ ∃ C, height C ≤ n ∧ Runs A C q

def Saturation : Prop :=
  ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (A : Automaton Q),
    reachable A (Fintype.card Q+1) = reachable A (Fintype.card Q)

def RunProductiveExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (A : Automaton Q) q,
    q ∈ productive A ↔ ∃ C, Runs A C q

def AcceptingProductiveExact : Prop :=
  ∀ (Q : Type) [Fintype Q] [LinearOrder Q] (A : Automaton Q),
    (∃ C q, Runs A C q ∧ A.accept q = true) ↔ ∃ q ∈ productive A, A.accept q = true

/-- Semantic emptiness characterization of the actually constructed source
difference. The iteration still contains genuine arithmetic existential queries. -/
def SourceDifferenceEmptyExact : Prop :=
  ∀ (M N : Machine) [LinearOrder M.State] [LinearOrder N.State],
    let D := difference (source M) (source N)
    Empty D ↔ ∀ q ∈ productive D, D.accept q = false

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductive.Targets
