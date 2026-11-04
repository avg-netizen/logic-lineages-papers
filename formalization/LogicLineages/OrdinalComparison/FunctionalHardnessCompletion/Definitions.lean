module
public import LogicLineages.OrdinalComparison.SourcePolynomialFamilyLiftDefinitions
public import LogicLineages.OrdinalComparison.SourceFiniteExponentProjectionDefinitions
@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion
open SourcePolynomialRealization SourceFiniteExponentProjection OriginalDomain

/-- A finite simultaneous system of linear equations over Z[X]. The shared
`Fin n` indexes the same polynomial unknown in every equation. Expression
syntax has fixed-coefficient shifts and sums, and no product of unknowns. -/
abbrev System (n : Nat) := List (SignedPair.Expression n)
abbrev Mask (n : Nat) := Fin n → Bool

/-- Executable complete list of zero patterns, including the empty pattern. -/
def masks : (n : Nat) → List (Mask n)
  | 0 => [fun i => Fin.elim0 i]
  | n+1 => (masks n).flatMap fun z =>
      [Fin.cases false z, Fin.cases true z]

/-- Keep every original index. Inactive variables are replaced in syntax,
uniformly at all occurrences in all equations, by an exact signed zero. -/
def restrict {n : Nat} (z : Mask n) : SignedPair.Expression n → SignedPair.Expression n
  | .unit => .unit
  | .var i => if z i then .var i else SignedPair.zeroExpression
  | .add a b => .add (restrict z a) (restrict z b)
  | .neg a => .neg (restrict z a)
  | .shift a => .shift (restrict z a)

def restrictSystem {n : Nat} (z : Mask n) (s : System n) : System n := s.map (restrict z)
def zeroExtend {n : Nat} {A : Type*} [Zero A] (z : Mask n) (x : Fin n → A) : Fin n → A :=
  fun i => if z i then x i else 0

def PolynomialSolves {n : Nat} (s : System n) (p : Fin n → NonnegativePolynomial) : Prop :=
  ∀ d ∈ s, polynomialMeaning (fun i => signedCoefficients (p i)) d = 0
def PolynomialSatisfiable {n : Nat} (s : System n) : Prop := ∃ p, PolynomialSolves s p

def OrdinalSolves {n : Nat} (s : System n) (ρ : AdmissibleSubstitution (SignedPair.Context n)) : Prop :=
  ∀ d ∈ s, SignedPair.meaning (SignedPair.inputs ρ) d = 0

/-- The exact finite-query semantic source endpoint. The existence of a
successful mask corresponds to disjunction of finitely many comparison-query
failures once alignment and conjunction are assembled. -/
def PatternOrdinalSatisfiable {n : Nat} (s : System n) : Prop :=
  ∃ z ∈ masks n, ∃ ρ : AdmissibleSubstitution (SignedPair.Context n),
    OrdinalSolves (restrictSystem z s) ρ

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion
