module
public import LogicLineages.OrdinalComparison.KernelMassKeyDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Actual eventual equivalence/order classes at equal genuine inputs. -/
def ActualPrincipalKernelMassKey : Prop :=
  ∀ eta : NONote, 0 < eta.1.repr → ∀ c e t : Nat,
    principalKernelMassModulus eta c e ≤ t →
      c+actualOrdinalNorm (Ordinal.omega0^eta.1.repr) ≤ t ∧
      e+actualOrdinalNorm (Ordinal.omega0^eta.1.repr) ≤ t ∧
      (actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t =
          actualSuffixKernel (Ordinal.omega0^eta.1.repr) e t ↔
        principalKernelMassKey eta c=principalKernelMassKey eta e) ∧
      (actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t <
          actualSuffixKernel (Ordinal.omega0^eta.1.repr) e t ↔
        principalKernelMassKey eta e < principalKernelMassKey eta c)

/-- The executable local same-input comparison actually returns the scalar
order on its proved tail; this is not the full two-sort comparison algorithm. -/
def ActualPrincipalKernelMassCompare : Prop :=
  ∀ eta : NONote, 0 < eta.1.repr → ∀ c e t : Nat,
    principalKernelMassModulus eta c e ≤ t →
      match principalKernelMassCompare eta c e with
      | .lt => actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t < actualSuffixKernel (Ordinal.omega0^eta.1.repr) e t
      | .eq => actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t = actualSuffixKernel (Ordinal.omega0^eta.1.repr) e t
      | .gt => actualSuffixKernel (Ordinal.omega0^eta.1.repr) e t < actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t

end LogicLineages.OrdinalComparison.Targets
