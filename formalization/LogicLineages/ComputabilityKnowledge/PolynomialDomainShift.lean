module

public import LogicLineages.ComputabilityKnowledge.PolynomialComparison

@[expose] public section

/-! Literal finite expansion of Xi−1, paper02's nonnegative-to-positive
convention (lines185–190). No terms are discarded: zero coefficients, repeated
monomials and repeated variable indices remain valid. Computation acts only on
explicit monomial codes, not an abstract polynomial quotient. -/
namespace LogicLineages.ComputabilityKnowledge.PolynomialDomainShift

open PositiveExpression PolynomialCircuit

def attachVariable (i : Nat) (m : Monomial) : Monomial := (m.1,i::m.2)
def negateCoefficient (m : Monomial) : Monomial := (-m.1,m.2)

/-- At each factor choose Xi or −1; the fold expands the literal product. -/
def expand (m : Monomial) : Monomials :=
  m.2.foldr (fun i ms => ms.map (attachVariable i) ++ ms.map negateCoefficient) [(m.1,[])]

def shiftTerms (ms : Monomials) : Monomials := ms.flatMap expand

def shift (p : Code) : Code := ⟨p.inputCount,shiftTerms p.monomials⟩

def finiteNat {n : Nat} (ν : Fin n → Nat) : Nat → Nat :=
  fun i => if h : i < n then ν ⟨i,h⟩ else 0

def toPositive {n : Nat} (ν : Fin n → Nat) : Fin n → PosNat :=
  fun i => ⟨ν i + 1,Nat.zero_lt_succ _⟩

def toNonnegative {n : Nat} (ρ : Fin n → PosNat) : Fin n → Nat :=
  fun i => (ρ i).val - 1

noncomputable def evalNonnegative (p : Code) (ν : Fin p.inputCount → Nat) : Int :=
  MvPolynomial.eval (fun i => (finiteNat ν i : Int)) (interpret p)

def HasNonnegativeRoot (p : Code) : Prop :=
  ∃ ν : Fin p.inputCount → Nat, evalNonnegative p ν = 0

def encodedShift (xs : List Nat) : Option (List Nat) :=
  (PolynomialCircuit.decode xs).map (fun p => PolynomialCircuit.encode (shift p))

end LogicLineages.ComputabilityKnowledge.PolynomialDomainShift
