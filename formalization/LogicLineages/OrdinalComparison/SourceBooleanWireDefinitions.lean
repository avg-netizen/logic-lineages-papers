module
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.List.OfFn
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BooleanWire

/-- Natural input wires already carry flattened arithmetic/source values.
Boolean references address preceding nodes only, so sharing is literal. -/
inductive Node (n m : Nat) where
  | eq (a c : Fin n) | le (a c : Fin n) | lt (a c : Fin n)
  | neg (c : Fin m) | conj (c d : Fin m) | disj (c d : Fin m)
  deriving DecidableEq

inductive Ref (n m : Nat) where
  | input (i : Fin n) | previous (i : Fin m)
  | output | aux (i : Fin 8) | zero | one
  deriving DecidableEq

/-- These are concrete natural arithmetic atoms, never predicate oracles.
Sort will subsequently be lowered by the actual source sorting theorem. -/
inductive Atom (n m : Nat) where
  | eq (a b : Ref n m)
  | add (a b c : Ref n m)
  | sort (a b low high : Ref n m)
  deriving DecidableEq

def bit (b : Bool) : Nat := if b then 1 else 0

def Ref.value {n m} (a : Fin n → Nat) (w : Fin m → Nat) (b : Nat)
    (z : Fin 8 → Nat) : Ref n m → Nat
  | .input i => a i
  | .previous i => w i
  | .output => b
  | .aux i => z i
  | .zero => 0
  | .one => 1

def Atom.Holds {n m} (a : Fin n → Nat) (w : Fin m → Nat) (b : Nat)
    (z : Fin 8 → Nat) : Atom n m → Prop
  | .eq x y => x.value a w b z = y.value a w b z
  | .add x y v => x.value a w b z + y.value a w b z = v.value a w b z
  | .sort x y l h =>
      l.value a w b z = min (x.value a w b z) (y.value a w b z) ∧
      h.value a w b z = max (x.value a w b z) (y.value a w b z)

def zeroAux {n m} : List (Atom n m) := List.ofFn (fun i : Fin 8 => .eq (.aux i) .zero)

/-- Uniform eight auxiliary wires, with every unused slot fixed to zero.
Equality sorts its inputs, computes their nonnegative difference, sorts that
with one, and complements the resulting minimum. Weak order tests max=a;
strict order complements the reverse weak-order test. -/
def constraints {n m} : Node n m → List (Atom n m)
  | .eq a c =>
      [.sort (.input a) (.input c) (.aux 0) (.aux 1),
       .add (.aux 0) (.aux 2) (.aux 1), .sort (.aux 2) .one (.aux 3) (.aux 4),
       .add .output (.aux 3) .one,
       .eq (.aux 5) .zero, .eq (.aux 6) .zero, .eq (.aux 7) .zero]
  | .le a c =>
      [.sort (.input a) (.input c) (.aux 0) (.aux 1),
       .sort (.aux 1) (.input c) (.aux 2) (.aux 3),
       .add (.aux 2) (.aux 4) (.aux 3), .sort (.aux 4) .one (.aux 5) (.aux 6),
       .add .output (.aux 5) .one, .eq (.aux 7) .zero]
  | .lt a c =>
      [.sort (.input c) (.input a) (.aux 0) (.aux 1),
       .sort (.aux 1) (.input a) (.aux 2) (.aux 3),
       .add (.aux 2) (.aux 4) (.aux 3), .sort (.aux 4) .one (.aux 5) (.aux 6),
       .add (.aux 7) (.aux 5) .one, .add .output (.aux 7) .one]
  | .neg c => .add .output (.previous c) .one :: zeroAux
  | .conj c d =>
      [.sort (.previous c) (.previous d) (.aux 0) (.aux 1), .eq .output (.aux 0),
       .eq (.aux 2) .zero, .eq (.aux 3) .zero, .eq (.aux 4) .zero,
       .eq (.aux 5) .zero, .eq (.aux 6) .zero, .eq (.aux 7) .zero]
  | .disj c d =>
      [.sort (.previous c) (.previous d) (.aux 0) (.aux 1), .eq .output (.aux 1),
       .eq (.aux 2) .zero, .eq (.aux 3) .zero, .eq (.aux 4) .zero,
       .eq (.aux 5) .zero, .eq (.aux 6) .zero, .eq (.aux 7) .zero]

def LocalHolds {n m} (a : Fin n → Nat) (w : Fin m → Nat) (g : Node n m)
    (b : Nat) (z : Fin 8 → Nat) : Prop := ∀ atom ∈ constraints g, atom.Holds a w b z

def evalNode {n m} (a : Fin n → Nat) (w : Fin m → Bool) : Node n m → Bool
  | .eq x y => decide (a x = a y)
  | .le x y => decide (a x ≤ a y)
  | .lt x y => decide (a x < a y)
  | .neg c => !(w c)
  | .conj c d => w c && w d
  | .disj c d => w c || w d

/-- Explicit total witness constructor. It uses only the referenced shared
input values, min/max, subtraction and constants. No search is performed. -/
def canonicalAux {n m} (a : Fin n → Nat) (w : Fin m → Nat) : Node n m → Fin 8 → Nat
  | .eq x y =>
      let l := min (a x) (a y); let h := max (a x) (a y); let δ := h-l
      ![l,h,δ,min δ 1,max δ 1,0,0,0]
  | .le x y =>
      let l := min (a x) (a y); let h := max (a x) (a y)
      let l' := min h (a y); let h' := max h (a y); let δ := h'-l'
      ![l,h,l',h',δ,min δ 1,max δ 1,0]
  | .lt x y =>
      let l := min (a y) (a x); let h := max (a y) (a x)
      let l' := min h (a x); let h' := max h (a x); let δ := h'-l'
      ![l,h,l',h',δ,min δ 1,max δ 1,1-min δ 1]
  | .neg _ => ![0,0,0,0,0,0,0,0]
  | .conj c d | .disj c d => ![min (w c) (w d),max (w c) (w d),0,0,0,0,0,0]

/-- A finite intrinsically acyclic shared DAG, one constructor per Boolean
node. The latest wire is index zero; old wires embed by Fin.succ. A reference
never duplicates the syntax of its producer. -/
inductive Dag (n : Nat) : Nat → Type where
  | nil : Dag n 0
  | snoc {m : Nat} (prior : Dag n m) (node : Node n m) : Dag n (m+1)

def evaluate {n} : {m : Nat} → Dag n m → (Fin n → Nat) → Fin m → Bool
  | _, .nil, _ => Fin.elim0
  | _, .snoc d g, a => Fin.cons (evalNode a (evaluate d a) g) (evaluate d a)

def witnesses {n} : {m : Nat} → Dag n m → (Fin n → Nat) → Fin m → Fin 8 → Nat
  | _, .nil, _ => Fin.elim0
  | _, .snoc d g, a =>
      Fin.cons (canonicalAux a (fun i => bit (evaluate d a i)) g) (witnesses d a)

def Holds {n} : {m : Nat} → Dag n m → (Fin n → Nat) →
    (Fin m → Nat) → (Fin m → Fin 8 → Nat) → Prop
  | _, .nil, _, _, _ => True
  | _, .snoc d g, a, w, z =>
      Holds d a (fun i => w i.succ) (fun i => z i.succ) ∧
      LocalHolds a (fun i => w i.succ) g (w 0) (z 0)

def atomCount {n} : {m : Nat} → Dag n m → Nat
  | _, .nil => 0
  | _, .snoc d g => atomCount d + (constraints g).length

def newWireCount {n} : {m : Nat} → Dag n m → Nat
  | _, .nil => 0
  | _, .snoc d _ => newWireCount d + 9
end LogicLineages.OrdinalComparison.Source.BooleanWire
