module
public import LogicLineages.StandardControlCurrent.NumericalKernelDefinitions
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Definitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.UniformSeparationTargets
open OrdinalComparison NumericalKernel
open OrdinalComparison.KernelSourceCompletion.UniformCompletion

/-- Literal scheduled source process equals the independently defined forced-first
numerical kernel on its broad first-budget domain, including the zero suffix. -/
def ScheduledCalibration : Prop := ∀ d c t : Nat, 1 ≤ d → c ≤ Phi t →
  KernelSourceCompletion.sourceCount d c t = count d c t ∧
  KernelSourceCompletion.sourceValue d c t = value d c t ∧
  (∀ j : Int, sourceSignedDepth d c j t = depth d c j t ∧
    sourceSignedValue d c j t = signed d c j t)

def UniformDepthAndOutputBounds : Prop :=
  ∀ d c e : Nat, ∀ j k : Int, ∀ R t : Nat, 3 ≤ d → region d c e j k R t →
    (Phi t : Int) ≤ depth d c j t ∧
    (Phi t : Int) ≤ depth d e k t ∧
    (Phi t : Int) ≤ depth d c j (t+1) ∧
    (Phi t : Int) ≤ depth d e k (t+1) ∧
    Phi t ≤ signed d c j t ∧ Phi t ≤ signed d e k t ∧
    Phi t ≤ signed d c j (t+1) ∧ Phi t ≤ signed d e k (t+1)

/-- The whole printed quantitative region, including signed j,k and arbitrary
required f-depth R. No genuine-input restriction on c,e is added. -/
def QuantitativeSeparation : Prop :=
  ∀ d c e : Nat, ∀ j k : Int, ∀ R t : Nat, 3 ≤ d → region d c e j k R t →
    (Phi^[R]) (signed d e k t) < signed d c j (t+1) ∧
    (c < e → (Phi^[R]) (signed d e k t) < signed d c j t)

def ExactSignedOrder : Prop :=
  ∀ d c t : Nat, 3 ≤ d → c ≤ Phi t → ∀ j k : Int,
    0 < depth d c j t → 0 < depth d c k t →
    (signed d c j t < signed d c k t ↔ j < k) ∧
    (signed d c j t = signed d c k t ↔ j = k) ∧
    (signed d c j t ≤ signed d c k t ↔ j ≤ k)

def EffectiveEqualityTail : Prop :=
  ∀ d c e : Nat, ∀ j k : Int, 3 ≤ d → ∀ t u : Nat,
    equalityTail d c e j k ≤ t → equalityTail d c e j k ≤ u →
    c ≤ Phi t ∧ e ≤ Phi u ∧
    0 < depth d c j t ∧ 0 < depth d e k u ∧
    (signed d c j t = signed d e k u ↔ t=u ∧ c=e ∧ j=k)

def UniformTailPrograms : Prop :=
  Primrec degreeConstant ∧ Primrec degreeThreshold ∧
  Primrec (fun p : Nat × Nat × Nat × Int × Int =>
    equalityTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

def Full : Prop := ScheduledCalibration ∧ UniformDepthAndOutputBounds ∧
  QuantitativeSeparation ∧ ExactSignedOrder ∧ EffectiveEqualityTail ∧ UniformTailPrograms
end LogicLineages.StandardControlCurrent.UniformSeparationTargets
