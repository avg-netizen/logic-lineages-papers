module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSourceComparisonDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LiteralFiniteSourceTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSourceComparisonTargets
open Source Source.OriginalDomain

/-- The literal paper08 theorem domain: original terms of the same type,
ground free variables, and finite-valued closed coefficients at every literal
collapse in coordinate zero of the computed canonical assignments. Universal
comparison ranges over the genuine WW admissible substitutions. -/
def OriginalComparisonDecision : Prop :=
  ∀ (Γ : List Ty), (∀ σ ∈ Γ, σ = Ty.ground) →
    ∀ τ (a b : OriginalTerm Γ τ),
      LiteralFiniteSource.finiteSource a → LiteralFiniteSource.finiteSource b →
      ∀ mode,
        ∃ (av bv : OrdinalVector Γ τ.level),
          AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a = some av ∧
          AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b = some bv ∧
          ((∀ ρ : AdmissibleSubstitution Γ, GroundAdmissibleComparison.relation mode av bv ρ) ↔
            FiniteSourceComparison.decide
              (Γ.length, mode, SyntaxCode.encodeTerm a, SyntaxCode.encodeTerm b) = true)

def TotalNumericDecision : Prop := Computable FiniteSourceComparison.decide

/-- Paper08, theorem finite-source, including effective source admission,
uniform total Boolean comparison, and the unbounded-internal-type
recursor-free inclusion. No BASE decision oracle is a premise. -/
def FullFiniteSourceComparison : Prop :=
  LiteralFiniteSourceTargets.ExactSourceTest ∧
  LiteralFiniteSourceTargets.RecursorFreePasses ∧
  Computable LiteralFiniteSource.Code.acceptsSource ∧
  TotalNumericDecision ∧ OriginalComparisonDecision

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSourceComparisonTargets
