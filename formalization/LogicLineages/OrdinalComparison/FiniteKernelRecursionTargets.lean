module
public import LogicLineages.OrdinalComparison.FiniteKernelRecursionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Source08 lem:kernel-recursion, exact genuine-domain suppliers.
The printed unrestricted signed d=2 recurrence is NOT this contract:
its child is undefined for every negative offset. This obstruction is
proved alongside the valid recurrence, with no whole-label promotion. -/
def ActualFiniteKernelBlockRecursion : Prop :=
  ∀ n c t : Nat, c + 2*(n+2) + 1 ≤ t →
    let parent := Ordinal.omega0 ^ ((n+2 : Nat) : Ordinal)
    let child := Ordinal.omega0 ^ ((n+1 : Nat) : Ordinal)
    let entry := actualSuffixKernel parent (c+n+2) t
    actualSuffixKernelCount parent c t =
      actualSuffixKernelCount child c entry +
        actualSuffixKernelCount parent (c+n+2) t ∧
    actualSuffixKernel parent c t = actualSuffixKernel child c entry

def ActualFiniteSignedBlockRecursion : Prop :=
  ∀ n c : Nat, ∀ j : Int, (1 ≤ n ∨ 0 ≤ j) → ∀ t : Nat,
    finiteKernelRecursionThreshold (n+2) c j ≤ t →
    let entry := actualSuffixKernel
      (Ordinal.omega0 ^ ((n+2 : Nat) : Ordinal)) (c+n+2) t
    0 < signedKernelDepth (n+2) c j t ∧
    0 < signedKernelDepth (n+1) c j entry ∧
    rawSignedKernelValue (n+2) c j t =
      rawSignedKernelValue (n+1) c j entry

def ActualFiniteQuadraticShift : Prop :=
  ∀ c t : Nat, c+3 ≤ t → ∀ j : Int,
    signedKernelDepth 2 c j t =
      ((Phi t / 2 : Nat) : Int) + (j - (((c+1)/2 : Nat) : Int)) + 1 ∧
    rawSignedKernelValue 2 c j t =
      rawQuadraticShift (j - (((c+1)/2 : Nat) : Int)) t

def ActualFiniteKernelPrograms : Prop :=
  Computable (fun p : Nat × Nat × Nat => encodedFiniteKernelCount p.1 p.2.1 p.2.2) ∧
  Computable (fun p : Nat × Nat × Nat => encodedFiniteKernelValue p.1 p.2.1 p.2.2) ∧
  ∀ d c t : Nat, 1 ≤ d → c+d+1 ≤ t →
    encodedFiniteKernelCount d c t =
      actualSuffixKernelCount (Ordinal.omega0 ^ (d : Ordinal)) c t ∧
    encodedFiniteKernelValue d c t =
      actualSuffixKernel (Ordinal.omega0 ^ (d : Ordinal)) c t

def ActualSignedDegreeTwoRecursionObstruction : Prop :=
  (∀ c t : Nat, c+2 ≤ t →
    signedKernelDepth 1 c (-1) t = 0) ∧
  (∀ c t : Nat, finiteKernelRecursionThreshold 2 c (-1) ≤ t →
    0 < signedKernelDepth 2 c (-1) t) ∧
  ∀ c : Nat, ¬ ∃ T : Nat, ∀ t : Nat, T ≤ t → c+2 ≤ t →
    0 < signedKernelDepth 1 c (-1) t

end LogicLineages.OrdinalComparison.Targets
