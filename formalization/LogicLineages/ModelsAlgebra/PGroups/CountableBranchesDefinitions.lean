module

public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDefinitions
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Logic.Equiv.Set

@[expose] public section

/-! Ordinary countable branch families reindexed into the unchanged subset-of-Nat
syntax. The encoding and its inverse are actual constructions. Choice is allowed;
no effective formula compiler or enumeration-correctness supplier is assumed. -/
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

noncomputable def branchEncoding (ι : Type) [Countable ι] : ι ↪ ℕ := by
  letI := Encodable.ofCountable ι
  exact ⟨Encodable.encode, Encodable.encode_injective⟩

noncomputable def branchIndices (ι : Type) [Countable ι] : Set ℕ :=
  Set.range (branchEncoding ι)

noncomputable def branchEquiv (ι : Type) [Countable ι] : ι ≃ branchIndices ι :=
  Equiv.ofInjective (branchEncoding ι) (branchEncoding ι).injective

noncomputable def countableDisjEx {ι : Type} [Countable ι] {n : ℕ}
    (m : ι → ℕ) (matrix : (i : ι) → Formula (n + m i)) : Formula n :=
  .disjEx (branchIndices ι) (fun k => m ((branchEquiv ι).symm k))
    (fun k => matrix ((branchEquiv ι).symm k))

noncomputable def countableConjAll {ι : Type} [Countable ι] {n : ℕ}
    (m : ι → ℕ) (matrix : (i : ι) → Formula (n + m i)) : Formula n :=
  .conjAll (branchIndices ι) (fun k => m ((branchEquiv ι).symm k))
    (fun k => matrix ((branchEquiv ι).symm k))

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
