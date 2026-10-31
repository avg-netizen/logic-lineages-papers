module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarStatementChecks
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Prod
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlow

/-- Occurrence counts for the literal binary and terminal grammar productions. -/
structure Counts (Q : Type) where
  binary : Q × Q → Nat
  terminal : Finset Q × Q → Nat

def terminalTotal {Q : Type} [Fintype Q] (c : Counts Q) (B : Finset Q) : Nat :=
  ∑ q, c.terminal (B,q)

def consumed {Q : Type} [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q)
    (c : Counts Q) (q : Q) : Nat :=
  (∑ p : Q × Q, if δ p.1 p.2 = q then c.binary p else 0) +
    ∑ B : Finset Q, c.terminal (B,q)

def produced {Q : Type} [Fintype Q] [DecidableEq Q] (c : Counts Q) (q : Q) : Nat :=
  ∑ p : Q × Q, c.binary p * ((if p.1 = q then 1 else 0) + (if p.2 = q then 1 else 0))

/-- Necessary exact production-flow equations. No sufficiency or connectivity
is hidden here: disconnected circulation is not claimed to be derivable. -/
def Realizes {Q : Type} [Fintype Q] [DecidableEq Q] (δ : Q → Q → Q)
    (q : Q) (w : List (Finset Q)) (c : Counts Q) : Prop :=
  (∀ B r, r ∉ B → c.terminal (B,r) = 0) ∧
  (∀ B, terminalTotal c B = w.count B) ∧
  ∀ r, consumed δ c r = (if q = r then 1 else 0) + produced c r

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlow
