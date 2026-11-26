module

public import LogicLineages.ComputabilityKnowledge.WWBoundedVectorCode
public import LogicLineages.ComputabilityKnowledge.Comparators.AffineParameterComparison
public import Mathlib.Computability.Partrec

@[expose] public section

/-! Paper 02, `cor:consumers` (Further exact consumers), for the repository's
original-O semantics at the published example control Φ(n) = F₅(n+100).
WW Definitions 2.1 and 2.4–2.8 supply the syntax, interpretation, admissible
substitutions, zero padding, comparisons and bounded norm. The printed paper
does not specify a universal quantifier over choices of Φ. A reading intended
to cover every permitted control needs a separately parameterized claim.

Programs receive prefix syntax. They must halt on every promised input,
including all negative instances. Semantic finiteness is an input promise,
with no proof, recognizer or translation supplied to the program. -/
namespace LogicLineages.ComputabilityKnowledge.Paper02FiniteVectorConsumerTargets

open WWOrdinalTermSemantics WWGroundAdmissibility WWBoundedVectorPadding

abbrev SourceVector (d : Nat) := List (Term (Fin d))
abbrev VectorCode := List (List Nat)

def encodeVector {d : Nat} (xs : SourceVector d) : VectorCode :=
  xs.map WWOrdinalPrefixCode.encode

/-- WW writes the finite-valued condition on a scalar as f ≺ ω. -/
def FiniteVector {d : Nat} (xs : SourceVector d) : Prop :=
  xs ≠ [] ∧ ∀ t ∈ xs, Comparison false t .omega

def VectorEquality {d : Nat} (xs ys : SourceVector d) : Prop :=
  ∀ i : Nat, Equality (component xs i) (component ys i)

def Answers (result : Part Bool) (claim : Prop) : Prop :=
  ∃ answer, answer ∈ result ∧ (answer = true ↔ claim)

/-- One program for all finite numbers d of independent ground variables. -/
def MultivariableEquality : Prop :=
  ∃ run : Nat × VectorCode × VectorCode → Part Bool, Partrec run ∧
    ∀ (d : Nat) (xs ys : SourceVector d), FiniteVector xs → FiniteVector ys →
      Answers (run (d, encodeVector xs, encodeVector ys)) (VectorEquality xs ys)

/-- Strict at component zero and weak above it, or weak everywhere. -/
def UnaryComparison : Prop :=
  ∃ run : Bool × VectorCode × VectorCode → Part Bool, Partrec run ∧
    ∀ (weak : Bool) (xs ys : SourceVector 1), FiniteVector xs → FiniteVector ys →
      Answers (run (weak, encodeVector xs, encodeVector ys))
        (if weak then VectorLE xs ys else VectorLT xs ys)

/-- Each component's source ordinal norm is compared with the zeroth norm. -/
def UnaryBoundedNorm : Prop :=
  ∃ run : VectorCode → Part Bool, Partrec run ∧
    ∀ xs : SourceVector 1, FiniteVector xs →
      Answers (run (encodeVector xs)) (VectorBoundedNorm xs)

/-- This reads the affine sentence in the positive-expression grammar of the
unary theorem cited in its proof. Its final conjunct is already checked. -/
def FurtherExactConsumersAtPublishedControl : Prop :=
  MultivariableEquality ∧ UnaryComparison ∧ UnaryBoundedNorm ∧
    Comparators.AffineParameterComparison.Target

/-- Direct evaluation of the original vectors along the specified positive
ray. The coordinate interpretation is independent of any code translator. -/
def AlongAffine {d : Nat} (weak : Bool) (as bs : List Nat)
    (h : AffineParameterSubstitution.Admissible d as bs) (xs ys : SourceVector d) : Prop :=
  ∀ (n : PositiveExpression.PosNat) (i : Nat),
    let ρ := AffineParameterComparison.valuation d as bs h n
    let value := fun t : Term (Fin d) => denote (fun j => ((ρ j : Nat) : Ordinal.{0})) t
    if weak || decide (0 < i) then value (component xs i) ≤ value (component ys i)
    else value (component xs i) < value (component ys i)

/-- Companion reading in which the affine sentence retains the preceding
finite-valued O-vector domain. The comparison is tested only along the ray,
while the input vectors satisfy the same semantic finiteness promise. -/
def AffineFiniteVectorComparison : Prop :=
  ∃ run : Bool × Nat × List Nat × List Nat × VectorCode × VectorCode → Part Bool, Partrec run ∧
    ∀ (weak : Bool) (d : Nat) (as bs : List Nat)
      (h : AffineParameterSubstitution.Admissible d as bs) (xs ys : SourceVector d),
      FiniteVector xs → FiniteVector ys →
        Answers (run (weak, d, as, bs, encodeVector xs, encodeVector ys))
          (AlongAffine weak as bs h xs ys)

end LogicLineages.ComputabilityKnowledge.Paper02FiniteVectorConsumerTargets
