module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Targets

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Targets

/-- The next input pays an arbitrary retained mass up to the preceding first
budget. This does not impose the companion's original-input domain. -/
def ShiftedSourceBudgetOrder : Prop :=
  ∀ t a b : Nat, a ≤ Phi t → ∀ i : Nat,
    sourceBudget b t i ≤ sourceBudget a (t+1) i

/-- Exact source-to-source block recursion at the broad first-budget domain.
The complete count of the inner process is retained. -/
def BroadSourceBlock : Prop := ∀ n c t : Nat, c+n+2 ≤ Phi t →
  let K := sourceValue (n+2) (c+n+2) t
  sourceValue (n+2) c t = sourceValue (n+1) c K ∧
  sourceCount (n+2) c t = sourceCount (n+1) c K + sourceCount (n+2) (c+n+2) t

/-- The unchanged numerical base case of the source uniform theorem. -/
def CubicUnsignedSeparation : Prop :=
  ∀ c e R t : Nat, 16 ≤ t → 9000*(c+e+R+1) ≤ Phi t →
    (Phi^[R]) (sourceValue 3 e t) < sourceValue 3 c (t+1) ∧
    (c < e → (Phi^[R]) (sourceValue 3 e t) < sourceValue 3 c t)

/-- Unsigned intermediate statement with exactly the printed constants and
region, before transporting arbitrary signed indices. -/
def UnsignedSeparation : Prop :=
  ∀ d c e R t : Nat, 3 ≤ d → region d c e 0 0 R t →
    (Phi^[R]) (sourceValue d e t) < sourceValue d c (t+1) ∧
    (c < e → (Phi^[R]) (sourceValue d e t) < sourceValue d c t)

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Targets
