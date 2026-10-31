module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerBooleanDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProduct
open RankedParse ProfileAutomatonEncoding ForestParseRepresentationCotree
open CotreePresburgerBoolean CotreePresburgerPullback

/-- Literal pair-state product. Component child counts are substituted by the
finite sum of pair-state counts projecting to them, then formulas are conjoined. -/
def product {Q R : Type} [Fintype Q] [LinearOrder Q] [Fintype R] [LinearOrder R]
    (A : Automaton Q) (B : Automaton R) : Automaton (Q ×ₗ R) where
  leaf := toLex (A.leaf,B.leaf)
  node o s :=
    pullFormula (fun t : Q ×ₗ R => (ofLex t).1) (A.node o (ofLex s).1) ⊓
    pullFormula (fun t : Q ×ₗ R => (ofLex t).2) (B.node o (ofLex s).2)
  accept s := A.accept (ofLex s).1 && B.accept (ofLex s).2

def difference {Q R : Type} [Fintype Q] [LinearOrder Q] [Fintype R] [LinearOrder R]
    (A : Automaton Q) (B : Automaton R) : Automaton (Q ×ₗ R) := product A (complement B)

def Empty {Q : Type} [DecidableEq Q] (A : Automaton Q) : Prop := ∀ C, ¬ Language A C

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProduct
