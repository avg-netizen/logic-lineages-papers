module
public import LogicLineages.OrdinalComparison.WWSourceFinitePositiveTargets
public import LogicLineages.OrdinalComparison.WWSourceScalarHeadProfileTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open SourceClasses ForwardTranslation AdmissibleSum AdmissibleAssignment
/-- Both clauses of foundations.tex cor:source-classes. Every fixed index is
collected from the actual successful scalar compiler, including nested shift
tails. Ground free names are explicit and the level restriction covers every
internal type and subtype, not merely the result type. -/
def ActualSourceClasses : Prop :=
  ActualRecursorFreePositiveFinite ∧
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ (τ : Ty) (p : Policy) (t : OriginalTerm Γ τ), InternalLevelBound 2 t →
      ∃ v : OrdinalVector Γ τ.level, assignment p t = some v ∧
        ∃ s : Scalar (OrdinalComponent Γ), compileScalar (v 0) = some s ∧
          ∀ c ∈ scalarHeads s, Order.IsSuccLimit (fixedHead c) ∧
            fixedHead c < Ordinal.omega0 ^ Ordinal.omega0
end LogicLineages.OrdinalComparison.Source.Targets
