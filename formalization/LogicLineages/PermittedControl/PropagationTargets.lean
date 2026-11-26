module
public import LogicLineages.PermittedControl.RelativeDescentDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Strict source rule: next upper budget compared with CURRENT lower budget. -/
def StrictPropagation : Prop := ∀ (mu nu u v : Ordinal.{0}) (S b c b' : Nat),
  mu+u < epsilonZero → nu+v < epsilonZero →
  actualOrdinalNorm mu ≤ S → actualOrdinalNorm nu ≤ S →
  actualOrdinalNorm u ≤ b → actualOrdinalNorm mu ≤ c →
  0 < actualLimitPart u → actualLimitPart u < actualLimitPart v → b+S ≤ b' →
  actualLimitPart u ≤ actualLimitPart (relativeMaximum nu (actualLimitPart v) b') ∧
  actualLimitPart (relativeMaximum mu (actualLimitPart u) c) < actualLimitPart u

/-- Weak source rule: next upper budget compared with NEXT lower budget. -/
def WeakPropagation : Prop := ∀ (mu nu u v : Ordinal.{0}) (S c b' : Nat),
  mu+u < epsilonZero → nu+v < epsilonZero →
  actualOrdinalNorm mu ≤ S → actualOrdinalNorm nu ≤ S → actualOrdinalNorm mu ≤ c →
  0 < actualLimitPart u → actualLimitPart v = actualLimitPart u → c+S ≤ b' →
  actualLimitPart (relativeMaximum mu (actualLimitPart u) c) ≤
    actualLimitPart (relativeMaximum nu (actualLimitPart v) b')

/-- Equal next budget and pointwise ordered actual profiles on all eligible
candidates. Affordability is the source running-recursion domain. -/
def OrderedProfilePropagation : Prop := ∀ (mu nu u v : Ordinal.{0}) (c : Nat),
  mu+u < epsilonZero → nu+v < epsilonZero →
  actualOrdinalNorm mu ≤ c → actualOrdinalNorm nu ≤ c →
  0 < actualLimitPart u → actualLimitPart v = actualLimitPart u →
  (∀ x : Ordinal.{0}, x < actualLimitPart u → relativeCost nu x ≤ relativeCost mu x) →
  actualLimitPart (relativeMaximum mu (actualLimitPart u) c) ≤
    actualLimitPart (relativeMaximum nu (actualLimitPart v) c)

/-- All three implications of source lem:propagation, on actual relative steps. -/
def Propagation : Prop := StrictPropagation ∧ WeakPropagation ∧ OrderedProfilePropagation

end LogicLineages.PermittedControl.Targets
