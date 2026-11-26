module
public import LogicLineages.CartierObserverCurrent.InitialPrincipalPartsDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.InitialPrincipalParts.Targets
open SplittingRoots RootInterpolation

def SourceDivisibility : Prop := ∀ d : Nat,
  splitPolynomial d ∣ (rootProduct d) ^ SourceBudget.budget d

def BoundedPresentation : Prop := ∀ d M : Nat, ∀ f : RatFunc (FieldAt d),
  bounded d M f ↔ ∃ U : Polynomial (FieldAt d),
    U.degree < ((rootProduct d) ^ M).degree ∧
    f = algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) U /
      algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) ((rootProduct d) ^ M)

/-- Uniqueness pays the polynomial part too; no properness assumption hides it. -/
def FullUniqueness : Prop := ∀ d M : Nat,
  ∀ q r : Polynomial (FieldAt d), ∀ b c : Coefficients d M,
    algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) q + reconstruct d M b =
      algebraMap (Polynomial (FieldAt d)) (RatFunc (FieldAt d)) r + reconstruct d M c →
    q = r ∧ b = c

/-- Actual complete coverage with zero polynomial part, including zero and empty cases. -/
def ProperCoverage : Prop := ∀ d M : Nat, ∀ f : RatFunc (FieldAt d),
  bounded d M f ↔ ∃! b : Coefficients d M, reconstruct d M b = f

/-- The initial source has unique actual coefficients, before any Cartier iteration. -/
def InitialSourceCoverage : Prop := ∀ d : Nat, 1 ≤ d →
  ∀ P : Polynomial (ZMod 2), P.degree < (SourceBudget.denominator (ZMod 2) d).degree →
    ∃! b : Coefficients d (SourceBudget.budget d),
      reconstruct d (SourceBudget.budget d) b = source d P
end LogicLineages.CartierObserverCurrent.InitialPrincipalParts.Targets
