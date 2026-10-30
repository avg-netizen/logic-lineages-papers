module
public import LogicLineages.OrdinalComparison.EncodedKernelWordDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def EncodedKernelWordComputable : Prop :=
  Computable₂ encodedKernelWordRun

/-- Exact closed-word folding, preserving both exit value and replacement
count. Source hypotheses are literal syntax validity and genuine input, not an
assumed evaluator or normalization-correctness field. -/
def EncodedKernelWordCorrect : Prop :=
  ∀ w : List (ONote × Nat), (∀ p ∈ w, ONote.NF p.1 ∧ 0 < p.1.repr) →
    ∀ t : Nat, actualPrincipalWordGenuine w t →
      encodedKernelWordRun (encodePrincipalKernelWord w) t=actualPrincipalWordRun w t

end LogicLineages.OrdinalComparison.Targets
