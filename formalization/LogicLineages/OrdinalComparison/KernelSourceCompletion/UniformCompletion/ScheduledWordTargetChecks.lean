module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.ScheduledWordTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.TargetChecks

example : Targets.ScheduledJointOrder =
  (∀ smallBudget bigBudget : Nat → Nat, ∀ a b : Ordinal.{0},
    a ≤ b → b < epsilonZero → (∀ i : Nat, smallBudget i ≤ bigBudget i) →
      actualScheduledCount smallBudget a ≤ actualScheduledCount bigBudget b) := rfl

example : Targets.ControlBudgetShiftOrder =
  (∀ B V a b : Nat, B < V → a ≤ V → ∀ i : Nat,
    sourceBudget b B i ≤ sourceBudget a V i) := rfl

example : Targets.SourceInputMassOrder =
  (∀ d c e t u : Nat, 1 ≤ d → c ≤ e → t ≤ u → e ≤ Phi t →
    c ≤ Phi u ∧ sourceCount d e t ≤ sourceCount d c u ∧
    sourceValue d e t ≤ sourceValue d c u ∧
    (t < u → sourceValue d e t < sourceValue d c u)) := rfl

example : Targets.ActualBroadChildWord =
  (∀ n c t : Nat, c ≤ Phi t →
    let d := n+2
    let B := Phi t
    let q := (B-c)/d
    let A := c+q*d
    let S := sourceValue (n+1) A t
    let word := principalKernelWord (List.replicate q (ONote.ofNat (n+1))) c
    let out := actualPrincipalWordRun word S
    A ≤ B ∧ B-A = (B-c)%d ∧ B-A < d ∧ B ≤ S ∧
    (q = 0 → out = (S,0)) ∧ actualPrincipalWordGenuine word S ∧
    sourceValue d c t = out.1 ∧
    sourceCount d c t = sourceCount (n+1) A t+out.2) := rfl

example : Targets.ScheduledWordSuppliers =
  (Targets.ScheduledJointOrder ∧ Targets.ControlBudgetShiftOrder ∧
    Targets.SourceInputMassOrder ∧ Targets.ActualBroadChildWord) := rfl

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.TargetChecks
