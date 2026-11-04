module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Definitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Targets

/-- Direct calibration beyond the companion input domain. Every trace/count
equality is a conclusion, with no old-count equality at original t asserted. -/
def FirstBudgetCalibration : Prop := ∀ d c t : Nat, 1 ≤ d → c ≤ Phi t →
  let Q := firstSuffix d c t
  Q < Ordinal.omega0 ^ (d : Ordinal) ∧ Q < epsilonZero ∧
  sourceState d c t 1 = Q ∧ c+actualOrdinalNorm Q = Phi t ∧
  sourceCount d c t = actualControlledCount (compensatedPrefixControl c) Q+1 ∧
  sourceValue d c t = (Phi^[actualControlledCount (compensatedPrefixControl c) Q]) (Phi t) ∧
  (∀ i : Nat, i ≤ sourceCount d c t-1 →
    sourceState d c t (i+1) = actualControlledStateAfter (compensatedPrefixControl c) Q i ∧
    c+actualOrdinalNorm (sourceState d c t (i+1)) = (Phi^[i+1]) t) ∧
  sourceState d c t (sourceCount d c t) < Ordinal.omega0 ∧
  (∀ i : Nat, i < sourceCount d c t → Ordinal.omega0 ≤ sourceState d c t i)

/-- Compatibility with the immutable accepted numeric representation, only
on its genuine domain. The broadened source process is never silently
identified with the padded companion at invalid original inputs. -/
def SignedAgreementOnGenuineDomain : Prop :=
  ∀ d c t : Nat, 1 ≤ d → c+d+1 ≤ t → ∀ j : Int,
    sourceSignedDepth d c j t = signedKernelDepth d c j t ∧
    sourceSignedValue d c j t = rawSignedKernelValue d c j t

/-- The strong literal integer-depth reading is separate from the numerical
output bounds. All four displayed choices of index/input are explicit. -/
def UniformDepthAndOutputBounds : Prop :=
  ∀ d c e : Nat, ∀ j k : Int, ∀ R t : Nat, 3 ≤ d → region d c e j k R t →
    (Phi t : Int) ≤ sourceSignedDepth d c j t ∧
    (Phi t : Int) ≤ sourceSignedDepth d e k t ∧
    (Phi t : Int) ≤ sourceSignedDepth d c j (t+1) ∧
    (Phi t : Int) ≤ sourceSignedDepth d e k (t+1) ∧
    Phi t ≤ sourceSignedValue d c j t ∧ Phi t ≤ sourceSignedValue d e k t ∧
    Phi t ≤ sourceSignedValue d c j (t+1) ∧ Phi t ≤ sourceSignedValue d e k (t+1)

/-- The whole printed quantitative region, including signed j,k and arbitrary
required f-depth R. No genuine-input restriction on c,e is added. -/
def QuantitativeSeparation : Prop :=
  ∀ d c e : Nat, ∀ j k : Int, ∀ R t : Nat, 3 ≤ d → region d c e j k R t →
    (Phi^[R]) (sourceSignedValue d e k t) < sourceSignedValue d c j (t+1) ∧
    (c < e → (Phi^[R]) (sourceSignedValue d e k t) < sourceSignedValue d c j t)

def ExactSignedOrder : Prop :=
  ∀ d c t : Nat, 3 ≤ d → c ≤ Phi t → ∀ j k : Int,
    0 < sourceSignedDepth d c j t → 0 < sourceSignedDepth d c k t →
    (sourceSignedValue d c j t < sourceSignedValue d c k t ↔ j < k) ∧
    (sourceSignedValue d c j t = sourceSignedValue d c k t ↔ j = k) ∧
    (sourceSignedValue d c j t ≤ sourceSignedValue d c k t ↔ j ≤ k)

def EffectiveEqualityTail : Prop :=
  ∀ d c e : Nat, ∀ j k : Int, 3 ≤ d → ∀ t u : Nat,
    equalityTail d c e j k ≤ t → equalityTail d c e j k ≤ u →
    c ≤ Phi t ∧ e ≤ Phi u ∧
    0 < sourceSignedDepth d c j t ∧ 0 < sourceSignedDepth d e k u ∧
    (sourceSignedValue d c j t = sourceSignedValue d e k u ↔ t=u ∧ c=e ∧ j=k)

def UniformTailPrograms : Prop :=
  Primrec degreeConstant ∧ Primrec degreeThreshold ∧
  Primrec (fun p : Nat × Nat × Nat × Int × Int =>
    equalityTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

/-- Fixed entire source goal for Option A. Startup calibration and the
compatibility bridge are separate suppliers to prove, never premises here. -/
def FullUniformSource : Prop :=
  UniformDepthAndOutputBounds ∧ QuantitativeSeparation ∧ ExactSignedOrder ∧
    EffectiveEqualityTail ∧ UniformTailPrograms

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Targets
