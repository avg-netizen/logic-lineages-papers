module
public import LogicLineages.OrdinalComparison.KernelConventionDiagnosticDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelReachableInputConvention
/-- Input-parameterized representation of exactly the same degree-two/mass-one
kernel. The diagnostic targets below specialize the original input to4. -/
noncomputable def initial (t : Nat) : Ordinal := actualSuffixKernelInitial (Ordinal.omega0 ^ (2 : Ordinal)) 1 t
def firstBudget (t : Nat) : Nat := Phi t - 1
def coefficient (t : Nat) : Nat := firstBudget t / 2
noncomputable def limitState (t : Nat) : Ordinal := Ordinal.omega0 * (coefficient t : Ordinal)
noncomputable def sharedState (t : Nat) : Ordinal := limitState t + 1
def secondBudget (t : Nat) : Nat := Phi (Phi t) - 1

/-- Exact first-state claims, with the input kept symbolic for proof transport. -/
def FirstData (t : Nat) : Prop :=
  1 < coefficient t ∧ firstBudget t % 2 = 1 ∧
  1 + actualOrdinalNorm (sharedState t) = Phi t ∧
  actualControlledStateAfter (compensatedPrefixControl 1) (initial t) 1 = sharedState t ∧
  KernelConventionDiagnostic.wholeStep (Ordinal.omega0 ^ (2 : Ordinal)) (firstBudget t) = sharedState t

/-- Exact second-transition claims, not complete-count or theorem refutation. -/
def SecondData (t : Nat) : Prop :=
  compensatedPrefixControl 1 (actualOrdinalNorm (sharedState t)) = secondBudget t ∧
  actualControlledStateAfter (compensatedPrefixControl 1) (initial t) 2 =
    actualMaximumPredecessor (limitState t) (secondBudget t) ∧
  KernelConventionDiagnostic.wholeStep (sharedState t) (secondBudget t) = limitState t ∧
  actualControlledStateAfter (compensatedPrefixControl 1) (initial t) 2 < limitState t ∧
  actualControlledStateAfter (compensatedPrefixControl 1) (initial t) 2 ≠
    KernelConventionDiagnostic.wholeStep (sharedState t) (secondBudget t)
end LogicLineages.OrdinalComparison.KernelReachableInputConvention
