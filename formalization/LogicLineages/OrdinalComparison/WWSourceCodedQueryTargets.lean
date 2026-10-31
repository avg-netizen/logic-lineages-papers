module
public import LogicLineages.OrdinalComparison.WWSourceCodedQueryDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open ForwardTranslation AdmissibleSum AdmissibleAssignment
/-- Exact successful code production and source-domain correspondence. This
is not a computability certificate for an arbitrary Policy.shape function. -/
def ActualSourceCodedQuery : Prop :=
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ (τ υ : Ty) (p : Policy) (strict : Bool) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
      ∃ av : OrdinalVector Γ τ.level, ∃ bv : OrdinalVector Γ υ.level, ∃ code : Nat,
        assignment p a = some av ∧ assignment p b = some bv ∧
        compileSourceCode p strict a b = some code ∧ queryArity code = Γ.length ∧
        (CodedQueryGood code ↔
          ∀ ρ : OrdinalComponent Γ → Nat, (∀ c, 0 < ρ c) → SourceComparisonAt strict av bv ρ)
end LogicLineages.OrdinalComparison.Source.Targets
