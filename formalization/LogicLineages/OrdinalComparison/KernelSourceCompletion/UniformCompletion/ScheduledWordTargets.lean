module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Definitions
public import LogicLineages.OrdinalComparison.PrincipalWordActionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Targets

/-- Actual first-finite counts for explicit schedules. Finite initial states,
zero budgets and equality cases are included; only the actual ordinal domain
and pointwise budget order are assumed, never a count/decision supplier. -/
def ScheduledJointOrder : Prop :=
  ∀ smallBudget bigBudget : Nat → Nat, ∀ a b : Ordinal.{0},
    a ≤ b → b < epsilonZero → (∀ i : Nat, smallBudget i ≤ bigBudget i) →
      actualScheduledCount smallBudget a ≤ actualScheduledCount bigBudget b

/-- The literal control pays an adverse retained mass up to the larger seed.
This is budget arithmetic; no kernel meaning is assigned to an invalid mass. -/
def ControlBudgetShiftOrder : Prop :=
  ∀ B V a b : Nat, B < V → a ≤ V → ∀ i : Nat,
    sourceBudget b B i ≤ sourceBudget a V i

/-- Weak mass/input order of the independent numerical source functions on
their actual new domain; increasing input gives strict value order. -/
def SourceInputMassOrder : Prop :=
  ∀ d c e t u : Nat, 1 ≤ d → c ≤ e → t ≤ u → e ≤ Phi t →
    c ≤ Phi u ∧ sourceCount d e t ≤ sourceCount d c u ∧
    sourceValue d e t ≤ sourceValue d c u ∧
    (t < u → sourceValue d e t < sourceValue d c u)

/-- Exact finite child-word calibration at the independently scheduled first
budget, including q=0 and zero first budget. The low seed remains an
INDEPENDENT sourceValue at mass A even when A>t. Every actual word-child
domain is derived; counts retain the complete low-remainder work. -/
def ActualBroadChildWord : Prop := ∀ n c t : Nat, c ≤ Phi t →
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
  sourceCount d c t = sourceCount (n+1) A t+out.2

def ScheduledWordSuppliers : Prop :=
  ScheduledJointOrder ∧ ControlBudgetShiftOrder ∧ SourceInputMassOrder ∧ ActualBroadChildWord

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Targets
