module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerAutomatonStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerPullbackDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerBoolean
open RankedParse ProfileAutomatonEncoding ForestParseRepresentationCotree CotreePresburger
open CotreePresburgerPullback

/-- A literal horizontal-formula automaton. All constructors below operate on
finite ordered input state types; no transition-correctness oracle is a field. -/
structure Automaton (Q : Type) where
  leaf : Q
  node : Operation → Q → PFormula Q
  accept : Q → Bool

inductive Runs {Q : Type} [DecidableEq Q] (A : Automaton Q) : Cotree → Q → Prop where
  | atom : Runs A .atom A.leaf
  | node {o n c} (v : Fin (n + 2) → Q) (q : Q)
      (children : ∀ i, Runs A (c i) (v i))
      (step : (A.node o q).Realize (wordCounts (List.ofFn v))) :
      Runs A (.node o n c) q

/-- All Boolean language operations are relative to the source's reduced-cotree domain. -/
def Language {Q : Type} [DecidableEq Q] (A : Automaton Q) (C : Cotree) : Prop :=
  Reduced C ∧ ∃ q, Runs A C q ∧ A.accept q = true

def CompleteDeterministic {Q : Type} [DecidableEq Q] (A : Automaton Q) : Prop :=
  ∀ C, Reduced C → ∃! q, Runs A C q

def source (M : Machine) [LinearOrder M.State] : Automaton (CotreePresburgerAutomaton.State M.State) where
  leaf := CotreePresburgerAutomaton.leafState M
  node := CotreePresburgerAutomaton.nodeFormula M
  accept := CotreePresburgerAutomaton.accept M

/-- Complement changes only the finite accepting table. -/
def complement {Q : Type} (A : Automaton Q) : Automaton Q :=
  ⟨A.leaf,A.node,fun q => !(A.accept q)⟩

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerBoolean
