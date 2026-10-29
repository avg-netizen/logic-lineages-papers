module
public import LogicLineages.OrdinalComparison.Definitions
public import Mathlib.SetTheory.Ordinal.FixedPoint

@[expose] public section

/-! Explicit representation obligations behind the notation-domain components.
Mathlib's hereditary notation documentation describes ordinals below epsilon
zero, but a prose description is not used as a surjectivity theorem. The source
epsilon zero is calibrated as the least fixed point of actual omega power.
-/

namespace LogicLineages.OrdinalComparison

noncomputable def epsilonZero : Ordinal.{0} :=
  Ordinal.nfp (fun a : Ordinal => Ordinal.omega0 ^ a) 0

namespace Targets

def EpsilonZeroCalibration : Prop :=
  Ordinal.omega0 ^ epsilonZero = epsilonZero ∧
    ∀ b : Ordinal, Ordinal.omega0 ^ b = b → epsilonZero ≤ b

def NormalRepresentationSound : Prop :=
  ∀ a : NONote, a.1.repr < epsilonZero

def NormalRepresentationComplete : Prop :=
  ∀ b : Ordinal, b < epsilonZero → ∃ a : NONote, a.1.repr = b

end Targets
end LogicLineages.OrdinalComparison
