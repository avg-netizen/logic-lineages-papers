module
public import LogicLineages.OrdinalComparison.PrefixTraceDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal initial suffix at total norm t with permanent numerical mass a. -/
noncomputable def actualSuffixKernelInitial (pi : Ordinal.{0}) (a t : Nat) : Ordinal :=
  pi + ((t - a - actualOrdinalNorm pi : Nat) : Ordinal)

/-- Actual number of nonfinite suffix replacements, using the paid norm-maximal
count recursion rather than a supplied kernel/count oracle. -/
noncomputable def actualSuffixKernelCount (pi : Ordinal.{0}) (a t : Nat) : Nat :=
  actualControlledCount (compensatedPrefixControl a) (actualSuffixKernelInitial pi a t)

/-- Total exit norm; its agreement with the real suffix trace is separately
proved. Source meaning is restricted to the genuine input domain. -/
noncomputable def actualSuffixKernel (pi : Ordinal.{0}) (a t : Nat) : Nat :=
  (Phi^[actualSuffixKernelCount pi a t]) t

end LogicLineages.OrdinalComparison
