module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarRanksDefinitions
public import Mathlib.ModelTheory.Arithmetic.Presburger.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Combinatorics.Colex
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Sum.Order
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburger
open FirstOrder Language CotreeGrammarFlow CotreeGrammarRanks

abbrev PTerm (α : Type) := Language.presburger.Term α
abbrev PFormula (α : Type) := Language.presburger.Formula α

/-- Deterministic finite enumeration: no choice-based `Finset.toList`. -/
def elements (α : Type) [Fintype α] [LinearOrder α] : List α :=
  Finset.univ.sort (· ≤ ·)

def sumAll {α β : Type} [Fintype β] [LinearOrder β] (f : β → PTerm α) : PTerm α :=
  ((elements β).map f).sum

def allList {α β : Type} (xs : List β) (f : β → PFormula α) : PFormula α :=
  xs.foldr (fun x rest => f x ⊓ rest) ⊤

def anyList {α β : Type} (xs : List β) (f : β → PFormula α) : PFormula α :=
  xs.foldr (fun x rest => f x ⊔ rest) ⊥

def allOf {α β : Type} [Fintype β] [LinearOrder β] (f : β → PFormula α) :=
  allList (elements β) f

def anyOf {α β : Type} [Fintype β] [LinearOrder β] (f : β → PFormula α) :=
  anyList (elements β) f

def truth {α : Type} (p : Prop) [Decidable p] : PFormula α := if p then ⊤ else ⊥
def positive {α : Type} (t : PTerm α) : PFormula α := (t.equal 0).not

/-- Explicit sorted indexing makes finite existential closure executable. -/
def existsOf {α β : Type} [Fintype β] [LinearOrder β]
    (φ : PFormula (α ⊕ β)) : PFormula α :=
  let e := (Fintype.orderIsoFinOfCardEq β rfl).toEquiv.symm
  (BoundedFormula.relabel (fun a => Sum.map id e a) φ).exs

/-- Witnesses are binary-production counts, terminal-production counts, and ranks. -/
abbrev Witness (Q : Type) := (Q ×ₗ Q) ⊕ₗ ((Colex (Finset Q) ×ₗ Q) ⊕ₗ Q)
abbrev Vars (Q : Type) := Finset Q ⊕ Witness Q

instance colexFinsetFintype (Q : Type) [Fintype Q] : Fintype (Colex (Finset Q)) :=
  inferInstanceAs (Fintype (Finset Q))
instance witnessFintype (Q : Type) [Fintype Q] : Fintype (Witness Q) :=
  inferInstanceAs (Fintype ((Q × Q) ⊕ ((Finset Q × Q) ⊕ Q)))

def binaryIndex {Q : Type} (r s : Q) : Witness Q := toLex (Sum.inl (toLex (r,s)))
def terminalIndex {Q : Type} (B : Finset Q) (q : Q) : Witness Q :=
  toLex (Sum.inr (toLex (Sum.inl (toLex (toColex B,q)))))
def rankIndex {Q : Type} (q : Q) : Witness Q :=
  toLex (Sum.inr (toLex (Sum.inr q)))

def binaryTerm {Q : Type} (r s : Q) : PTerm (Vars Q) := .var (.inr (binaryIndex r s))
def terminalTerm {Q : Type} (B : Finset Q) (q : Q) : PTerm (Vars Q) :=
  .var (.inr (terminalIndex B q))
def rankTerm {Q : Type} (q : Q) : PTerm (Vars Q) := .var (.inr (rankIndex q))

def decodeCounts {Q : Type} (v : Witness Q → Nat) : Counts Q where
  binary p := v (binaryIndex p.1 p.2)
  terminal p := v (terminalIndex p.1 p.2)
def decodeRank {Q : Type} (v : Witness Q → Nat) : Q → Nat := fun q => v (rankIndex q)

section Finite
variable {Q : Type} [Fintype Q] [LinearOrder Q]

def terminalTotalTerm (B : Finset Q) : PTerm (Vars Q) := sumAll (terminalTerm B)
def consumedTerm (δ : Q → Q → Q) (q : Q) : PTerm (Vars Q) :=
  sumAll (fun r => sumAll (fun s => if δ r s = q then binaryTerm r s else 0)) +
  sumAll (fun B : Colex (Finset Q) => terminalTerm (ofColex B) q)
def producedTerm (q : Q) : PTerm (Vars Q) :=
  sumAll (fun r => sumAll (fun s =>
    (if r = q then binaryTerm r s else 0) + (if s = q then binaryTerm r s else 0)))

def flowFormula (δ : Q → Q → Q) (root : Q) : PFormula (Vars Q) :=
  allOf (fun B : Colex (Finset Q) => allOf (fun r : Q =>
    (truth (r ∉ ofColex B)).imp ((terminalTerm (ofColex B) r).equal 0))) ⊓
  allOf (fun B : Colex (Finset Q) =>
    (terminalTotalTerm (ofColex B)).equal (.var (.inl (ofColex B)))) ⊓
  allOf (fun q : Q => (consumedTerm δ q).equal
    ((if root = q then 1 else 0) + producedTerm q))

def edgeFormula (δ : Q → Q → Q) (p q : Q) : PFormula (Vars Q) :=
  anyOf (fun r : Q => anyOf (fun s : Q =>
    positive (binaryTerm r s) ⊓ truth (δ r s = p) ⊓ truth (r = q ∨ s = q)))

def ranksFormula (δ : Q → Q → Q) (root : Q) : PFormula (Vars Q) :=
  (rankTerm root).equal 1 ⊓ allOf (fun q : Q => (truth (q ≠ root)).imp
    (((consumedTerm δ q).equal 0 ⊓ (rankTerm q).equal 0) ⊔
     (positive (consumedTerm δ q) ⊓ anyOf (fun p : Q =>
       positive (rankTerm p) ⊓ (rankTerm q).equal (rankTerm p + 1) ⊓ edgeFormula δ p q))))

/-- Actual finite first-order formula in the signature (0,1,+), with existential
production-count/rank witnesses. Instantiating `Q := Fin n` takes exactly a
finite transition table and start-state index as input. No finite state space
is numerically evaluated here. This is construction, not a QE procedure. -/
def formula (δ : Q → Q → Q) (root : Q) : PFormula (Finset Q) :=
  existsOf (flowFormula δ root ⊓ ranksFormula δ root)

/-- Exact constraints; reconstruction of a derivation is a separate theorem. -/
def Constraints (δ : Q → Q → Q) (root : Q) (counts : Finset Q → Nat)
    (c : Counts Q) (rank : Q → Nat) : Prop :=
  (∀ B r, r ∉ B → c.terminal (B,r) = 0) ∧
  (∀ B, terminalTotal c B = counts B) ∧
  (∀ q, consumed δ c q = (if root = q then 1 else 0) + produced c q) ∧
  RankedSupport δ root c rank
end Finite
end LogicLineages.ModelsAlgebra.Forests.CotreePresburger
