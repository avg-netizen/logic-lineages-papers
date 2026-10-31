module
public import LogicLineages.ModelsAlgebra.PGroups.PiConjunctionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

/-- Literal conjunction including the genuine rank-zero case. -/
noncomputable def piJoin {n : ℕ} : Formula n → Formula n → Formula n
  | .qf p, .qf q => .qf (.and p q)
  | φ, ψ => piConjunction φ ψ

noncomputable def piTruth (α : Ordinal.{0}) (n : ℕ) : Formula n :=
  if α=0 then .qf (.equal .zero .zero) else piQF (.equal .zero .zero)

/-- Finite membership guards for an actual finite quantified witness block. -/
noncomputable def piFiniteGuard (α : Ordinal.{0}) {n : ℕ} : List (Formula n) → Formula n
  | [] => piTruth α n
  | φ :: fs => piJoin φ (piFiniteGuard α fs)
end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
