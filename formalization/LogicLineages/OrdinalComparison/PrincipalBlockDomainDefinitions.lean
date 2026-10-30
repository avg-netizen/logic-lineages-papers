module
public import LogicLineages.OrdinalComparison.PrincipalBlocksDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Ordinary ordinal sum, in the displayed left-to-right block order. -/
noncomputable def principalBlockSum (es : List ONote) : Ordinal :=
  (es.map fun e => Ordinal.omega0 ^ e.repr).sum

/-- Transparent source CNF-block domain, with repeated equal exponents allowed.
It contains only syntax normality, positive exponents, and their displayed order. -/
def GenuinePrincipalBlocks (es : List ONote) : Prop :=
  (∀ e ∈ es, ONote.NF e ∧ 0 < e.repr) ∧
  es.Pairwise (fun e f => f.repr ≤ e.repr)

end LogicLineages.OrdinalComparison
