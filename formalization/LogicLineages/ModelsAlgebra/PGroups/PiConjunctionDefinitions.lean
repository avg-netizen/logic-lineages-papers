module

public import LogicLineages.ModelsAlgebra.PGroups.CountableBranchesDefinitions

@[expose] public section

/-! Literal Pi conjunction assembly. Normal-form Pi roots are flattened
without raising rank; other inputs get a literal zero-block conjunction
with no unsupported same-rank claim. QF-to-Pi1 normalization uses explicit
accepted padding, not a reassignment of the frozen rank-zero syntax. -/
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

def piOneNormalize {n : ℕ} : Formula n → Formula n
  | .qf q => piQF q
  | φ => φ

noncomputable def ordinaryConjunction {n : ℕ} (φ ψ : Formula n) : Formula n :=
  countableConjAll (fun _ : Bool => 0) (fun b => if b then ψ else φ)

noncomputable def piConjunction {n : ℕ} : Formula n → Formula n → Formula n
  | .conjAll s m matrix, .conjAll t l other =>
      countableConjAll (ι := s ⊕ t) (Sum.elim m l)
        (fun k => match k with
          | .inl i => matrix i
          | .inr i => other i)
  | φ, ψ => ordinaryConjunction φ ψ

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
