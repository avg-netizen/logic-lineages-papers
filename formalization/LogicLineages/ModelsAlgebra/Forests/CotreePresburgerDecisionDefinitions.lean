module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerNormalizeStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerDecision
open CotreePresburgerLinear CotreePresburgerUnit

/-- Finite first-order affine syntax. Every binder ranges over Nat, even when
prefix coordinates are interpreted in Int for the elimination invariant. -/
inductive Formula : Nat → Type where
  | atom {n : Nat} : Atom n → Formula n
  | bot {n : Nat} : Formula n
  | neg {n : Nat} : Formula n → Formula n
  | conj {n : Nat} : Formula n → Formula n → Formula n
  | ex {n : Nat} : Formula (n + 1) → Formula n

def Realize : {n : Nat} → Formula n → (Fin n → Int) → Prop
  | _, .atom a, v => a.eval v = true
  | _, .bot, _ => False
  | _, .neg p, v => ¬ Realize p v
  | _, .conj p q, v => Realize p v ∧ Realize q v
  | _, .ex p, v => ∃ x : Nat, Realize p (Fin.snoc v (x : Int))

/-- Total structural quantifier elimination; the existential branch invokes
the verified finite cutpoint/residue construction, not a tactic or oracle. -/
def quantifierFree : {n : Nat} → Formula n → QF n
  | _, .atom a => .atom a
  | _, .bot => .bot
  | _, .neg p => .neg (quantifierFree p)
  | _, .conj p q => .conj (quantifierFree p) (quantifierFree q)
  | _, .ex p => CotreePresburgerNormalize.eliminate (quantifierFree p)

def evaluate {n : Nat} (p : Formula n) (v : Fin n → Int) : Bool :=
  evalQF (quantifierFree p) v

/-- Existentially close all prefix variables over Nat in last-coordinate order. -/
def close : {n : Nat} → Formula n → Formula 0
  | 0, p => p
  | _ + 1, p => close (.ex p)

def satisfiable {n : Nat} (p : Formula n) : Bool :=
  evaluate (close p) Fin.elim0
end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerDecision
