module

public import LogicLineages.ComputabilityKnowledge.CircuitReduction
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename

@[expose] public section

/-!
# Explicit integer-polynomial monomial codes and positive circuits

Paper02 lines 191–198. Repeated variable indices represent powers; repeated
monomials are allowed. Empty variable lists are constants and the empty
monomial list is the zero polynomial. Interpretation is an actual Mathlib
MvPolynomial over Int, not a custom solvability predicate.
The compiler initializes both accumulators to one, skips zero coefficients,
and uses only positive constants, addition and multiplication. Original input
indices are shared; every emitted gate writes the next fresh circuit wire.
Coverage of arbitrary finite-variable polynomials is a separate mathematical
statement and is NOT claimed to compute codes from an arbitrary quotient value.
-/
namespace LogicLineages.ComputabilityKnowledge.PolynomialCircuit

open PositiveExpression CircuitReduction
abbrev Monomial := Int × List Nat
abbrev Monomials := List Monomial

structure Code where
  inputCount : Nat
  monomials : Monomials
  deriving DecidableEq

def Code.WellFormed (p : Code) : Prop :=
  ∀ m ∈ p.monomials, ∀ i ∈ m.2, i < p.inputCount

noncomputable def variableProduct : List Nat → MvPolynomial Nat Int
  | [] => 1
  | i :: is => MvPolynomial.X i * variableProduct is

noncomputable def interpretTerms : Monomials → MvPolynomial Nat Int
  | [] => 0
  | (z,vs) :: ms => MvPolynomial.C z * variableProduct vs + interpretTerms ms

noncomputable def interpret (p : Code) : MvPolynomial Nat Int := interpretTerms p.monomials

def productValue (ρ : Nat → PosNat) : List Nat → Nat
  | [] => 1
  | i :: is => (ρ i).val * productValue ρ is

def positiveTotal (ρ : Nat → PosNat) : Monomials → Nat
  | [] => 0
  | (z,vs) :: ms => z.toNat * productValue ρ vs + positiveTotal ρ ms

def negativeTotal (ρ : Nat → PosNat) : Monomials → Nat
  | [] => 0
  | (z,vs) :: ms => (-z).toNat * productValue ρ vs + negativeTotal ρ ms

/-- The accumulator at `acc` is multiplied by each original input in order;
the successive new wires are acc+1,acc+2,... . -/
def multiplyInputs : Nat → List Nat → List Gate
  | _, [] => []
  | acc, i :: is => .mul acc i :: multiplyInputs (acc + 1) is

/-- Parameter k denotes magnitude k+1, never a zero constant. -/
def monomialGates (start k : Nat) (vs : List Nat) : List Gate :=
  .constant k :: multiplyInputs start vs

structure State where
  gates : List Gate
  left : Nat
  right : Nat
  deriving DecidableEq

def initial (n : Nat) : State := ⟨[.constant 0,.constant 0],n,n+1⟩

def emit (n : Nat) (positive : Bool) (s : State) (k : Nat) (vs : List Nat) : State :=
  let start := n + s.gates.length
  let valueWire := start + vs.length
  let sumWire := valueWire + 1
  let old := if positive then s.left else s.right
  let gs := s.gates ++ monomialGates start k vs ++ [.add old valueWire]
  if positive then ⟨gs,sumWire,s.right⟩ else ⟨gs,s.left,sumWire⟩

def step (n : Nat) (s : State) : Monomial → State
  | (.ofNat 0,_) => s
  | (.ofNat (k+1),vs) => emit n true s k vs
  | (.negSucc k,vs) => emit n false s k vs

def build (p : Code) : State := p.monomials.foldl (step p.inputCount) (initial p.inputCount)

def compile (p : Code) : Circuit :=
  let s := build p
  ⟨p.inputCount,s.gates,s.left,s.right⟩

/-- Coefficient tag0,k means k; tag1,k means -(k+1), avoiding negative-zero
ambiguity. Each variable list has its explicit length frame. -/
def encodeTerms : Monomials → List Nat
  | [] => []
  | (.ofNat k,vs) :: ms => 0 :: k :: vs.length :: (vs ++ encodeTerms ms)
  | (.negSucc k,vs) :: ms => 1 :: k :: vs.length :: (vs ++ encodeTerms ms)

def decodeTerms : List Nat → Option Monomials
  | [] => some []
  | tag :: k :: len :: rest =>
    if len ≤ rest.length then
      match tag with
      | 0 => (decodeTerms (rest.drop len)).map ((Int.ofNat k,rest.take len) :: ·)
      | 1 => (decodeTerms (rest.drop len)).map ((Int.negSucc k,rest.take len) :: ·)
      | _ => none
    else none
  | _ => none
termination_by xs => xs.length
decreasing_by
  all_goals
    simp only [List.length_drop, List.length_cons]
    omega

def encode (p : Code) : List Nat := p.inputCount :: encodeTerms p.monomials

def decode : List Nat → Option Code
  | [] => none
  | n :: rest => (decodeTerms rest).map (fun ms => ⟨n,ms⟩)

def compileCode (xs : List Nat) : Option (List Nat) :=
  (decode xs).map (fun p => CircuitReduction.encodeCircuit (compile p))

end LogicLineages.ComputabilityKnowledge.PolynomialCircuit
