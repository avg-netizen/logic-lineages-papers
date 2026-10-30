module
public import LogicLineages.OrdinalComparison.PrincipalBlocksDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 lem:peakword (409–425), first executable extraction stage.
No kernel evaluation or word-composition assertion is hidden in this data. -/
def ActualPrincipalBlocksDenotation : Prop :=
  ∀ o : ONote, ONote.NF o →
    ((principalExponentBlocks o).map fun e => Ordinal.omega0 ^ e.repr).sum = o.repr ∧
    principalBlocksWeight (principalExponentBlocks o) = actualOrdinalNorm o.repr

def ActualPrincipalBlocksNormalOrder : Prop :=
  ∀ o : ONote, ONote.NF o →
    (∀ e ∈ principalExponentBlocks o, ONote.NF e) ∧
    (principalExponentBlocks o).Pairwise (fun e f => f.repr ≤ e.repr)

def ActualPrincipalBlocksLimitDomain : Prop :=
  ∀ o : ONote, ONote.NF o → Order.IsSuccLimit o.repr →
    principalExponentBlocks o ≠ [] ∧
    ∀ e ∈ principalExponentBlocks o, 0 < e.repr

end LogicLineages.OrdinalComparison.Targets
