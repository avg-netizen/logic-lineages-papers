module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerTransitionStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.CotreeMachineParikhStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationStatesStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerAutomaton
open RankedParse ProfileAutomatonEncoding ForestParseRepresentationCotree
open ForestParseRepresentationStates CotreePresburger FirstOrder Language

/-- Root-kind tags are 0 for a leaf, 1 for union, and 2 for join. -/
def opKind : Operation → Fin 3
  | .union => 1
  | .join => 2

def kind : Cotree → Fin 3
  | .atom => 0
  | .node o _ _ => opKind o

abbrev State (Q : Type) := Fin 3 ×ₗ Colex (Finset Q)
instance stateFintype (Q : Type) [Fintype Q] : Fintype (State Q) :=
  inferInstanceAs (Fintype (Fin 3 × Finset Q))

def mkState {Q : Type} (k : Fin 3) (S : Finset Q) : State Q := toLex (k,toColex S)
def stateKind {Q : Type} (s : State Q) : Fin 3 := (ofLex s).1
def stateSubset {Q : Type} (s : State Q) : Finset Q := ofColex (ofLex s).2

def allowed {Q : Type} (o : Operation) (s : State Q) : Bool := decide (stateKind s ≠ opKind o)

def leafState (M : Machine) : State M.State := mkState 0 {M.leaf}

/-- Actual finite horizontal formula table, not an assumed state-set transition. -/
def nodeFormula (M : Machine) [LinearOrder M.State] (o : Operation) (s : State M.State) :
    PFormula (State M.State) :=
  truth (stateKind s = opKind o) ⊓
    CotreePresburgerTransition.horizontalFormula (M.node o) (stateSubset s) stateSubset (allowed o)

def accept (M : Machine) [DecidableEq M.State] (s : State M.State) : Bool :=
  decide (∃ q ∈ stateSubset s, M.accept q = true)

/-- Runs are generated only by the actual computed formulas. -/
inductive Runs (M : Machine) [LinearOrder M.State] : Cotree → State M.State → Prop where
  | atom : Runs M .atom (leafState M)
  | node {o n c} (v : Fin (n + 2) → State M.State) (s : State M.State)
      (children : ∀ i, Runs M (c i) (v i))
      (step : (nodeFormula M o s).Realize (fun a => (List.ofFn v).count a)) :
      Runs M (.node o n c) s

/-- Semantic comparison state, used in correctness proofs only. -/
noncomputable def expected (M : Machine) (C : Cotree) : State M.State :=
  mkState (kind C) (stateSet M C)

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerAutomaton
