module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerLinearStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit
open CotreePresburgerLinear

/-- Finite Boolean syntax; no quantification or semantic oracle. -/
inductive Boolean (A : Type) where
  | bot : Boolean A
  | top : Boolean A
  | atom : A → Boolean A
  | neg : Boolean A → Boolean A
  | conj : Boolean A → Boolean A → Boolean A
  | disj : Boolean A → Boolean A → Boolean A

namespace Boolean

def eval {A : Type} (f : A → Bool) : Boolean A → Bool
  | .bot => false
  | .top => true
  | .atom a => f a
  | .neg p => !(eval f p)
  | .conj p q => eval f p && eval f q
  | .disj p q => eval f p || eval f q

def map {A B : Type} (f : A → B) : Boolean A → Boolean B
  | .bot => .bot
  | .top => .top
  | .atom a => .atom (f a)
  | .neg p => .neg (map f p)
  | .conj p q => .conj (map f p) (map f q)
  | .disj p q => .disj (map f p) (map f q)

def atoms {A : Type} : Boolean A → List A
  | .bot | .top => []
  | .atom a => [a]
  | .neg p => atoms p
  | .conj p q | .disj p q => atoms p ++ atoms q

def disjoin {A : Type} (xs : List (Boolean A)) : Boolean A := xs.foldr .disj .bot
end Boolean

/-- Positive modulus is represented by `m+1`; every AST value is well formed. -/
inductive Atom (n : Nat) where
  | nonneg : Affine n → Atom n
  | dvd : Nat → Affine n → Atom n

namespace Atom

def eval {n : Nat} (v : Fin n → Int) : Atom n → Bool
  | .nonneg t => decide (0 ≤ t.eval v)
  | .dvd m t => decide (((m + 1 : Nat) : Int) ∣ t.eval v)
end Atom

abbrev QF (n : Nat) := Boolean (Atom n)
def evalQF {n : Nat} (p : QF n) (v : Fin n → Int) : Bool := p.eval (Atom.eval v)

inductive Sign where
  | neg | zero | pos
  deriving DecidableEq

def Sign.value : Sign → Int
  | .neg => -1
  | .zero => 0
  | .pos => 1

/-- The distinguished variable has intrinsically unit/zero coefficient.
All other variables occur in the genuine finite affine remainder. -/
inductive UnitAtom (n : Nat) where
  | nonneg : Sign → Affine n → UnitAtom n
  | dvd : Nat → Sign → Affine n → UnitAtom n

namespace UnitAtom

def eval {n : Nat} (v : Fin n → Int) (x : Int) : UnitAtom n → Bool
  | .nonneg s t => decide (0 ≤ s.value * x + t.eval v)
  | .dvd m s t => decide (((m + 1 : Nat) : Int) ∣ s.value * x + t.eval v)

def period {n : Nat} : UnitAtom n → Nat
  | .nonneg _ _ => 1
  | .dvd m _ _ => m + 1

def cutoffs {n : Nat} : UnitAtom n → List (Affine n)
  | .nonneg .pos t => [Affine.scale (-1) t]
  | .nonneg .neg t => [Affine.add t (Affine.const 1)]
  | _ => []

def subst {n : Nat} (b : Affine n) : UnitAtom n → Atom n
  | .nonneg s t => .nonneg (Affine.add (Affine.scale s.value b) t)
  | .dvd m s t => .dvd m (Affine.add (Affine.scale s.value b) t)
end UnitAtom

abbrev UnitFormula (n : Nat) := Boolean (UnitAtom n)
def evalUnit {n : Nat} (u : UnitFormula n) (v : Fin n → Int) (x : Int) : Bool :=
  u.eval (UnitAtom.eval v x)

def period {n : Nat} (u : UnitFormula n) : Nat := (u.atoms.map UnitAtom.period).prod
def cutoffs {n : Nat} (u : UnitFormula n) : List (Affine n) :=
  Affine.const 0 :: u.atoms.flatMap UnitAtom.cutoffs

def instantiate {n : Nat} (u : UnitFormula n) (b : Affine n) : QF n :=
  u.map (UnitAtom.subst b)

/-- The nonnegative guard is essential: quantification is over Nat, not Int. -/
def guarded {n : Nat} (u : UnitFormula n) : UnitFormula n :=
  .conj (.atom (.nonneg .pos (Affine.const 0))) u

/-- A conservative Cooper-style candidate construction. Every inequality's
cutpoint is retained, as is zero. No negative-infinity case is used because
`guarded` explicitly excludes negative witnesses. All ranges are finite. -/
def eliminate {n : Nat} (u : UnitFormula n) : QF n :=
  Boolean.disjoin ((cutoffs u).flatMap (fun b => (List.range (period u)).map
    (fun j => instantiate (guarded u) (Affine.add b (Affine.const (j : Int))))))

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerUnit
