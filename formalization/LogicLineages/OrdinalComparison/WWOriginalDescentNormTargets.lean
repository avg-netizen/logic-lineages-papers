module
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain

/-! Exact child-norm estimates used by the repaired first-free-subtree proof.
Exponential heads cost at most two; additive/exponential tails and both scalar
collapse children cost at most one. All values use actual admissible source
substitutions. The original collapse norm premise is not needed for these
stronger arithmetic inequalities, and is not replaced in the domain grammar. -/
def OriginalAddChildNorm : Prop :=
  ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution Γ) (i : Nat) (f g : OrdinalExpression Γ),
    AmbientGrade Γ i f → AmbientGrade Γ i g →
    actualOrdinalNorm (expressionValue ρ f) ≤ actualOrdinalNorm (expressionValue ρ (.add f g)) ∧
    actualOrdinalNorm (expressionValue ρ g) ≤ actualOrdinalNorm (expressionValue ρ (.add f g))

def OriginalExpChildNorm : Prop :=
  ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution Γ) (i : Nat) (f g : OrdinalExpression Γ),
    0 < i → AmbientGrade Γ (i + 1) f → AmbientGrade Γ i g →
    actualOrdinalNorm (expressionValue ρ f) ≤ 2 * actualOrdinalNorm (expressionValue ρ (.emul f g)) ∧
    actualOrdinalNorm (expressionValue ρ g) ≤ actualOrdinalNorm (expressionValue ρ (.emul f g))

def OriginalCollapseChildNorm : Prop :=
  ∀ (Γ : List Ty) (ρ : AdmissibleSubstitution Γ) (f g : OrdinalExpression Γ),
    AmbientGrade Γ 1 f → AmbientGrade Γ 0 g →
    actualOrdinalNorm (expressionValue ρ f) ≤ actualOrdinalNorm (expressionValue ρ (.collapse f g)) ∧
    actualOrdinalNorm (expressionValue ρ g) ≤ actualOrdinalNorm (expressionValue ρ (.collapse f g))

end LogicLineages.OrdinalComparison.Source.Targets
