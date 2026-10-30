module
public import LogicLineages.OrdinalComparison.KernelSuccessorNormalizeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Actual finite normalization stops at the matching exponent or a genuine
limit still above it; it never jumps below the requested principal. -/
def ActualKernelSuccessorNormalizeStructure : Prop :=
  ∀ eta mu : NONote, 0 < mu.1.repr → mu.1.repr ≤ eta.1.repr → ∀ c : Nat,
    let word := (kernelSuccessorNormalize eta mu c).1
    word ≠ [] ∧
    (∀ p ∈ word, ONote.NF p.1 ∧ mu.1.repr ≤ p.1.repr ∧ p.1.repr ≤ eta.1.repr) ∧
    ∃ pre last, word=pre++[(last,c)] ∧
      (last.repr=mu.1.repr ∨ Order.IsSuccLimit last.repr)

/-- Exact whole word action and replacement-count conservation on the computed
genuine-input tail. The kernel evaluator itself is not claimed computable. -/
def ActualKernelSuccessorNormalizeAction : Prop :=
  ∀ eta mu : NONote, 0 < mu.1.repr → mu.1.repr ≤ eta.1.repr → ∀ c t : Nat,
    (kernelSuccessorNormalize eta mu c).2 ≤ t →
      c+actualOrdinalNorm (Ordinal.omega0^eta.1.repr) ≤ t ∧
      actualPrincipalWordGenuine (kernelSuccessorNormalize eta mu c).1 t ∧
      actualPrincipalWordRun (kernelSuccessorNormalize eta mu c).1 t =
        (actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t,
          actualSuffixKernelCount (Ordinal.omega0^eta.1.repr) c t)

end LogicLineages.OrdinalComparison.Targets
