module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Targets

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.TargetChecks

example : degreeConstant 3 = 9000 := rfl
example : degreeThreshold 3 = 16 := rfl
example : degreeThreshold 4 = 900400 := rfl

example (d : Nat) : degreeConstant d = 1000*d^2 := by
  simp only [degreeConstant,pow_two,Nat.mul_assoc]

example (d : Nat) (hd : 4 ≤ d) : degreeThreshold d =
    max (degreeThreshold (d-1)) (100*degreeConstant (d-1)+100*d) := by
  cases d with
  | zero => omega
  | succ d =>
    rw [degreeThreshold,if_neg (by omega)]
    simp only [Nat.add_sub_cancel]

example (d c e : Nat) (j k : Int) (R t : Nat) :
    region d c e j k R t = (degreeThreshold d ≤ t ∧
      1000*d*d*(c+e+j.natAbs+k.natAbs+R+1) ≤ Phi t) := rfl

example : Targets.FirstBudgetCalibration = (∀ d c t : Nat, 1 ≤ d → c ≤ Phi t →
  let Q := firstSuffix d c t
  Q < Ordinal.omega0 ^ (d : Ordinal) ∧ Q < epsilonZero ∧
  sourceState d c t 1 = Q ∧ c+actualOrdinalNorm Q = Phi t ∧
  sourceCount d c t = actualControlledCount (compensatedPrefixControl c) Q+1 ∧
  sourceValue d c t = (Phi^[actualControlledCount (compensatedPrefixControl c) Q]) (Phi t) ∧
  (∀ i : Nat, i ≤ sourceCount d c t-1 →
    sourceState d c t (i+1) = actualControlledStateAfter (compensatedPrefixControl c) Q i ∧
    c+actualOrdinalNorm (sourceState d c t (i+1)) = (Phi^[i+1]) t) ∧
  sourceState d c t (sourceCount d c t) < Ordinal.omega0 ∧
  (∀ i : Nat, i < sourceCount d c t → Ordinal.omega0 ≤ sourceState d c t i)) := rfl

example : Targets.SignedAgreementOnGenuineDomain =
  (∀ d c t : Nat, 1 ≤ d → c+d+1 ≤ t → ∀ j : Int,
    sourceSignedDepth d c j t = signedKernelDepth d c j t ∧
    sourceSignedValue d c j t = rawSignedKernelValue d c j t) := rfl

/-- Independent expanded comparator: every source clause, quantitative
parameter, signed index and effectivity assertion is visible before proof. -/
example : Targets.FullUniformSource =
  ((∀ d c e : Nat, ∀ j k : Int, ∀ R t : Nat, 3 ≤ d → region d c e j k R t →
    (Phi t : Int) ≤ sourceSignedDepth d c j t ∧
    (Phi t : Int) ≤ sourceSignedDepth d e k t ∧
    (Phi t : Int) ≤ sourceSignedDepth d c j (t+1) ∧
    (Phi t : Int) ≤ sourceSignedDepth d e k (t+1) ∧
    Phi t ≤ sourceSignedValue d c j t ∧ Phi t ≤ sourceSignedValue d e k t ∧
    Phi t ≤ sourceSignedValue d c j (t+1) ∧ Phi t ≤ sourceSignedValue d e k (t+1)) ∧
  (∀ d c e : Nat, ∀ j k : Int, ∀ R t : Nat, 3 ≤ d → region d c e j k R t →
    (Phi^[R]) (sourceSignedValue d e k t) < sourceSignedValue d c j (t+1) ∧
    (c < e → (Phi^[R]) (sourceSignedValue d e k t) < sourceSignedValue d c j t)) ∧
  (∀ d c t : Nat, 3 ≤ d → c ≤ Phi t → ∀ j k : Int,
    0 < sourceSignedDepth d c j t → 0 < sourceSignedDepth d c k t →
    (sourceSignedValue d c j t < sourceSignedValue d c k t ↔ j < k) ∧
    (sourceSignedValue d c j t = sourceSignedValue d c k t ↔ j = k) ∧
    (sourceSignedValue d c j t ≤ sourceSignedValue d c k t ↔ j ≤ k)) ∧
  (∀ d c e : Nat, ∀ j k : Int, 3 ≤ d → ∀ t u : Nat,
    equalityTail d c e j k ≤ t → equalityTail d c e j k ≤ u →
    c ≤ Phi t ∧ e ≤ Phi u ∧
    0 < sourceSignedDepth d c j t ∧ 0 < sourceSignedDepth d e k u ∧
    (sourceSignedValue d c j t = sourceSignedValue d e k u ↔ t=u ∧ c=e ∧ j=k)) ∧
  Primrec degreeConstant ∧ Primrec degreeThreshold ∧
  Primrec (fun p : Nat × Nat × Nat × Int × Int =>
    equalityTail p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) := rfl

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.TargetChecks
