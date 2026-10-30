module
public import LogicLineages.OrdinalComparison.PrincipalKernelWordDefinitions
public import LogicLineages.OrdinalComparison.PrincipalBlockDomainDefinitions
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Actual semantic word action, returning total exit norm and the sum of
literal nonfinite replacement counts. This is not the executable compiler. -/
noncomputable def actualPrincipalWordRun : List (ONote × Nat) → Nat → Nat × Nat
  | [], t => (t, 0)
  | (e, a) :: w, t =>
      let next := actualSuffixKernel (Ordinal.omega0 ^ e.repr) a t
      let out := actualPrincipalWordRun w next
      (out.1, actualSuffixKernelCount (Ordinal.omega0 ^ e.repr) a t + out.2)

/-- Every dynamically reached kernel input satisfies its actual source domain.
This predicate is a conclusion of calibration, never an oracle premise. -/
noncomputable def actualPrincipalWordGenuine : List (ONote × Nat) → Nat → Prop
  | [], _ => True
  | (e, a) :: w, t =>
      a + actualOrdinalNorm (Ordinal.omega0 ^ e.repr) ≤ t ∧
      actualPrincipalWordGenuine w (actualSuffixKernel (Ordinal.omega0 ^ e.repr) a t)

end LogicLineages.OrdinalComparison
