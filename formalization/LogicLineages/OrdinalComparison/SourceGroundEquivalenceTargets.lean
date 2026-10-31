module
public import LogicLineages.OrdinalComparison.SourceGroundEquivalenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundEquivalence.Targets
open OriginalDomain SourceCollisionCompletion
/-- Whole cor:ground-equivalence via stronger constant-sized one-hole source
contexts. Literal source DAG inputs remain present once, including repeated
internal references. Both directions are actual full-assignment comparisons.
No use of the pending general Boolean compiler is assumed. -/
def FullGroundEquivalence : Prop :=
  (∀ Γ (a b : OriginalTerm Γ .ground) (ρ : AdmissibleSubstitution Γ),
    (rawScalar (valuation ρ) a ≤ rawScalar (valuation ρ) b ↔
      rawScalar (valuation ρ) (lower a) < rawScalar (valuation ρ) (upper b)) ∧
    (rawScalar (valuation ρ) a < rawScalar (valuation ρ) b ↔
      rawScalar (valuation ρ) (upper a) ≤ rawScalar (valuation ρ) (lower b))) ∧
  (∀ Γ (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (a b : OriginalTerm Γ .ground),
    (Weak a b ↔ Strict (lower a) (upper b)) ∧
    (Strict a b ↔ Weak (upper a) (lower b))) ∧
  (∀ Γ (d : Input Γ .ground),
    (lowerInput d).term=lower d.term ∧ (upperInput d).term=upper d.term ∧
    (lowerInput d).specs.length=d.specs.length+6 ∧ (upperInput d).specs.length=d.specs.length+6 ∧
    (lowerGraft d).term=lower d.term ∧ (upperGraft d).term=upper d.term ∧
    (lowerGraft d).input=d ∧ (upperGraft d).input=d ∧
    (lowerGraft d).context.holes=1 ∧ (upperGraft d).context.holes=1 ∧
    (lowerGraft d).nodes=d.specs.length+6 ∧ (upperGraft d).nodes=d.specs.length+6)
end LogicLineages.OrdinalComparison.Source.GroundEquivalence.Targets
