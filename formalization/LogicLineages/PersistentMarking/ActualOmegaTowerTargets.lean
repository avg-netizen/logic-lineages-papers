module

public import LogicLineages.PersistentMarking.ActualOmegaTowerDefinitions

@[expose] public section

/-! Unconditional ordinal facts about Paper 16's actual Ω-power index sequence.
No collapse function, coefficient norm, calibration, BH value, or inductive
accessibility premise is supplied or assumed here. The separate identity with
the epsilon-function endpoint is not part of this target. -/

namespace LogicLineages.PersistentMarking.ActualOmegaTower
open scoped Ordinal

def LiteralRecurrence : Prop :=
  omegaIndex = ω₁ ∧ argument 0 = 0 ∧ argument 1 = 1 ∧ argument 2 = omegaIndex ∧
    ∀ n, argument (n + 1) = omegaIndex ^ argument n

def StrictlyIncreasing : Prop := StrictMono argument

def BelowEndpoint : Prop := ∀ n, argument n < endpoint

def Cofinal : Prop :=
  ∀ a : Ordinal.{0}, a < endpoint ↔ ∃ n, a < argument n

def EndpointAsNfp : Prop := endpoint = Ordinal.nfp powerStep 0

def EndpointFixedPoint : Prop := omegaIndex ^ endpoint = endpoint

/-- The endpoint is below every pre-fixed point, hence every fixed point. -/
def EndpointLeast : Prop :=
  ∀ a : Ordinal.{0}, omegaIndex ^ a ≤ a → endpoint ≤ a

def FullActualOmegaTower : Prop :=
  LiteralRecurrence ∧ StrictlyIncreasing ∧ BelowEndpoint ∧ Cofinal ∧
    EndpointAsNfp ∧ EndpointFixedPoint ∧ EndpointLeast

end LogicLineages.PersistentMarking.ActualOmegaTower
