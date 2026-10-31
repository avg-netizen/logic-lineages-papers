module
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.List.Perm.Basic

/-! The literal finite grammar in repaired paper03's Parikh-transition proof.
A terminal is an entire finite subset of machine states, not an individual
state. The ordered terminal word retains all equal child occurrences.
`Builds` is the exact selected-state binary skeleton relation; it does not
postulate a Presburger predicate or canonical cotree correctness. -/
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammar

variable {Q : Type}

inductive Builds (δ : Q → Q → Q) : Q → List (Finset Q) → Prop where
  | leaf (B : Finset Q) (q : Q) : q ∈ B → Builds δ q [B]
  | node {r s : Q} {u v : List (Finset Q)} :
      Builds δ r u → Builds δ s v → Builds δ (δ r s) (u ++ v)

def binaryRule (δ : Q → Q → Q) (r s : Q) : ContextFreeRule (Finset Q) Q :=
  ⟨δ r s, [.nonterminal r, .nonterminal s]⟩

def terminalRule (q : Q) (B : Finset Q) : ContextFreeRule (Finset Q) Q :=
  ⟨q, [.terminal B]⟩

def rules [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) :
    Finset (ContextFreeRule (Finset Q) Q) :=
  Finset.univ.biUnion (fun r : Q => Finset.univ.image (binaryRule δ r)) ∪
    Finset.univ.biUnion (fun B : Finset Q => B.image (fun q => terminalRule q B))

def grammar [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q) (q : Q) :
    ContextFreeGrammar (Finset Q) := ⟨Q, q, rules δ⟩

def counts [DecidableEq Q] (w : List (Finset Q)) (B : Finset Q) : Nat := w.count B

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammar
