module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.Definitions
public import Mathlib.Computability.RE
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion

/-- A signed integer coefficient, fixed power of X, and optional unknown index.
`none` is a constant monomial. This input syntax has no unknown multiplication. -/
abbrev MonomialCode := Int × Nat × Option Nat
abbrev SystemCode := Nat × List (List MonomialCode)

def monomialOfCode (n : Nat) (m : MonomialCode) : Option (SignedPair.Monomial n) :=
  match m.2.2 with
  | none => some ⟨m.1, m.2.1, none⟩
  | some i => if h : i < n then some ⟨m.1, m.2.1, some ⟨i,h⟩⟩ else none

/-- Every occurrence is checked against the one shared unknown dimension. -/
def WellFormedCode (c : SystemCode) : Prop :=
  ∀ row ∈ c.2, ∀ m ∈ row, ∀ i, m.2.2 = some i → i < c.1

def systemOfCode (c : SystemCode) : System c.1 :=
  c.2.map fun row => SignedPair.fromMonomials (row.filterMap (monomialOfCode c.1))

/-- Invalid decodings or out-of-range unknown references are outside the
language. Zero polynomials and an empty simultaneous system are allowed. -/
def encodedPolynomialSolvable (e : Nat) : Prop :=
  ∃ c : SystemCode, Encodable.decode e = some c ∧
    WellFormedCode c ∧ PolynomialSatisfiable (systemOfCode c)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion
