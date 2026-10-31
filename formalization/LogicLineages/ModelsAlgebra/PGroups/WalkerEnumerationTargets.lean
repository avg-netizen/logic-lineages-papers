module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerEnumerationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Every countable source ordinal's entire decreasing-node tree has a finite
or natural enumeration with every ancestor earlier. This neither truncates
the tree nor bounds its branching or transfinite height. -/
def walkerOrdinalEnumeration : Prop :=
  ∀ ξ : Ordinal.{0}, ∀ [Countable ξ.ToType],
    (∃ (n : ℕ) (e : Fin n ≃ WalkerOrdinalNode ξ),
      StrictMono (fun i => walkerOrdinalCode ξ (e i)) ∧ WalkerAncestorEnumeration ξ (Fin n) e) ∨
    (∃ e : ℕ ≃ WalkerOrdinalNode ξ,
      StrictMono (fun i => walkerOrdinalCode ξ (e i)) ∧ WalkerAncestorEnumeration ξ ℕ e)

end LogicLineages.ModelsAlgebra.PGroups.Targets
