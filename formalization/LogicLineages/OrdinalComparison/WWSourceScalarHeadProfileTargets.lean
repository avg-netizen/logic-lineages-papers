module
public import LogicLineages.OrdinalComparison.WWSourceScalarHeadProfileDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open SourceClasses ForwardTranslation AdmissibleSum AdmissibleAssignment

def ExtractedPositiveHeadProfile : Prop :=
  ∀ (Γ : List Ty) (t : OrdinalExpression Γ) (c : ClosedPositive),
    extractPositive t = some c → positiveHeadHeight c = headHeight t

def CompiledScalarHeadProfile : Prop :=
  ∀ (Γ : List Ty) (t : OrdinalExpression Γ) (s : Scalar (OrdinalComponent Γ)) (L : Nat),
    compileScalar t = some s → headHeight t ≤ L →
      ∀ c ∈ scalarHeads s, positiveHeadHeight c + 1 ≤ L

def ActualLevelTwoSourceHeadProfile : Prop :=
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ (τ : Ty) (p : Policy) (t : OriginalTerm Γ τ), InternalLevelBound 2 t →
      ∃ v : OrdinalVector Γ τ.level, assignment p t = some v ∧
        ∃ s : Scalar (OrdinalComponent Γ), compileScalar (v 0) = some s ∧
          ∀ c ∈ scalarHeads s, positiveHeadHeight c ≤ 1
end LogicLineages.OrdinalComparison.Source.Targets
