module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarFlowStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOpen
open CotreeGrammarFlow

/-- Genuine partial derivations. Holes are unexpanded nonterminals; every
non-hole constructor is a legal production of the actual grammar. -/
inductive Tree {Q : Type} (δ : Q → Q → Q) : Q → Type where
  | hole (q : Q) : Tree δ q
  | terminal (B : Finset Q) (q : Q) (h : q ∈ B) : Tree δ q
  | branch {r s : Q} : Tree δ r → Tree δ s → Tree δ (δ r s)

def holes {Q : Type} {δ : Q → Q → Q} {q} : Tree δ q → List Q
  | .hole q => [q]
  | .terminal _ _ _ => []
  | .branch l r => holes l ++ holes r

def word {Q : Type} {δ : Q → Q → Q} {q} : Tree δ q → List (Finset Q)
  | .hole _ => []
  | .terminal B _ _ => [B]
  | .branch l r => word l ++ word r

def zeroCounts (Q : Type) : Counts Q := ⟨fun _ => 0, fun _ => 0⟩

def addCounts {Q : Type} (a b : Counts Q) : Counts Q :=
  ⟨fun p => a.binary p + b.binary p, fun p => a.terminal p + b.terminal p⟩

def counts {Q : Type} [DecidableEq Q] {δ : Q → Q → Q} {q} : Tree δ q → Counts Q
  | .hole _ => zeroCounts Q
  | .terminal B q _ => CotreeGrammarFlow.Proof.leafCounts B q
  | @Tree.branch _ _ r s l t => CotreeGrammarFlow.Proof.nodeCounts r s (counts l) (counts t)

/-- An actual one-distinguished-hole zipper, allowing partial sibling trees.
The indices record the root and the distinguished hole state exactly. -/
inductive Context {Q : Type} (δ : Q → Q → Q) : Q → Q → Type where
  | hole (q : Q) : Context δ q q
  | left {r s q} : Context δ r q → Tree δ s → Context δ (δ r s) q
  | right {r s q} : Tree δ r → Context δ s q → Context δ (δ r s) q

def plug {Q : Type} {δ : Q → Q → Q} {r q} (C : Context δ r q) (t : Tree δ q) : Tree δ r :=
  match C with
  | .hole _ => t
  | .left C s => .branch (plug C t) s
  | .right s C => .branch s (plug C t)

def contextCounts {Q : Type} [DecidableEq Q] {δ : Q → Q → Q} {r q}
    (C : Context δ r q) : Counts Q := counts (plug C (.hole q))

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarOpen
