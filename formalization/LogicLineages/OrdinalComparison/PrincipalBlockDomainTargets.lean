module
public import LogicLineages.OrdinalComparison.PrincipalBlockDomainDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 lem:peakword: genuine sorted block sums and exact prefix-split
bounds. Empty lists and repeated equal exponents are retained. -/
def ActualPrincipalBlockSumDomain : Prop :=
  ∀ es : List ONote, GenuinePrincipalBlocks es →
    principalBlockSum es < epsilonZero ∧
    actualOrdinalNorm (principalBlockSum es) = principalBlocksWeight es ∧
    (es ≠ [] → Order.IsSuccLimit (principalBlockSum es))

def ActualPrincipalBlockUpperBound : Prop :=
  ∀ es : List ONote, ∀ d : Ordinal.{0}, 0 < d →
    (∀ e ∈ es, e.repr ≤ d) → ∀ n : Nat,
      principalBlockSum es + (n : Ordinal) < Ordinal.omega0 ^ (d + 1)

end LogicLineages.OrdinalComparison.Targets
