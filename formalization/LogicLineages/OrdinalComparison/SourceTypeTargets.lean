module
public import LogicLineages.OrdinalComparison.SourceTypes

@[expose] public section

/-! Independently written exact components of the source's simple-type
conventions. Finite type support alone is not the whole finite comparator
closure lemma, which still requires the source/observation constructions. -/

namespace LogicLineages.OrdinalComparison.Source.Targets

def GroundArityLevel : Prop :=
  ∀ k : Nat, (Ty.curriedGround (k + 1)).level = 1

def TypeSubexpressionClosure : Prop :=
  ∀ σ τ : Ty, τ ∈ σ.subtypes → ∀ υ : Ty, υ ∈ τ.subtypes → υ ∈ σ.subtypes

end LogicLineages.OrdinalComparison.Source.Targets
