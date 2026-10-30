module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Union

/-! Carter v1 §2.2's finite-label full-binary tree automata. Trees here are
ordered syntax, with a separate literal recursive unordered equivalence.
These are not order forests, cotrees, or topological-embedding structures. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.CarterAutomata

inductive BinaryLabelTree (k : Nat) where
  | leaf : Fin k → BinaryLabelTree k
  | node : Fin k → BinaryLabelTree k → BinaryLabelTree k → BinaryLabelTree k
  deriving DecidableEq

inductive UnorderedEquivalent {k : Nat} : BinaryLabelTree k → BinaryLabelTree k → Prop
  | leaf (a : Fin k) : UnorderedEquivalent (.leaf a) (.leaf a)
  | node {a : Fin k} {l r l' r' : BinaryLabelTree k} :
      UnorderedEquivalent l l' → UnorderedEquivalent r r' →
      UnorderedEquivalent (.node a l r) (.node a l' r')
  | swap {a : Fin k} {l r l' r' : BinaryLabelTree k} :
      UnorderedEquivalent l r' → UnorderedEquivalent r l' →
      UnorderedEquivalent (.node a l r) (.node a l' r')

structure Automaton (k q : Nat) where
  leafState : Fin k → Fin q
  nodeState : Fin k → Fin q → Fin q → Fin q
  accepting : Finset (Fin q)

def Symmetric {k q : Nat} (M : Automaton k q) : Prop :=
  ∀ a x y, M.nodeState a x y = M.nodeState a y x

def run {k q : Nat} (M : Automaton k q) : BinaryLabelTree k → Fin q
  | .leaf a => M.leafState a
  | .node a l r => M.nodeState a (run M l) (run M r)

def height {k : Nat} : BinaryLabelTree k → Nat
  | .leaf _ => 1
  | .node _ l r => 1 + max (height l) (height r)

def accepts {k q : Nat} (M : Automaton k q) (t : BinaryLabelTree k) : Prop :=
  run M t ∈ M.accepting

def reachStep {k q : Nat} (M : Automaton k q) (S : Finset (Fin q)) : Finset (Fin q) :=
  S ∪ Finset.univ.image M.leafState ∪
    Finset.univ.biUnion (fun a => S.biUnion (fun x => S.image (M.nodeState a x)))

def reachable {k q : Nat} (M : Automaton k q) : Nat → Finset (Fin q)
  | 0 => ∅
  | n + 1 => reachStep M (reachable M n)

/-- True exactly when the accepted tree language is empty (correctness separate).
No unbounded search, oracle, or classical decision is used by this function. -/
def languageEmpty {k q : Nat} (M : Automaton k q) : Bool :=
  decide (reachable M q ∩ M.accepting = ∅)

end LogicLineages.ModelsAlgebra.Forests.CarterAutomata
