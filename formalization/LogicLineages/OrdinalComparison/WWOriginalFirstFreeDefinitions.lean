module
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain

/-- Original Definition 2.8 bounded norm, under actual bounded B substitutions.
No partial-output or first-free-subterm bound is part of this definition. -/
def BoundedVector {Γ : List Ty} {m : Nat} (h : OrdinalVector Γ m) : Prop :=
  ∀ (ρ : AdmissibleSubstitution Γ) (j : Fin (m + 1)),
    actualOrdinalNorm (expressionValue ρ (h j)) ≤ actualOrdinalNorm (expressionValue ρ (h 0))

/-- Literal first-wholly-head-free recursion paths. A free input stops before
any constructor is inspected. Active paths follow only the actual partial's
Add, positive Exp, and scalar collapse clauses. Neither norm inequalities nor
grade membership is hidden in the path definition. -/
inductive FirstFree (Γ : List Ty) (σ : Ty) :
    Nat → OrdinalExpression (σ :: Γ) → Nat → OrdinalExpression (σ :: Γ) → Prop where
  | stop {i : Nat} {t : OrdinalExpression (σ :: Γ)} :
      ordinalHeadFree t = true → FirstFree Γ σ i t i t
  | addLeft {i j : Nat} {f g u : OrdinalExpression (σ :: Γ)} :
      ordinalHeadFree (.add f g) = false → FirstFree Γ σ i f j u →
        FirstFree Γ σ i (.add f g) j u
  | addRight {i j : Nat} {f g u : OrdinalExpression (σ :: Γ)} :
      ordinalHeadFree (.add f g) = false → FirstFree Γ σ i g j u →
        FirstFree Γ σ i (.add f g) j u
  | expHead {i j : Nat} {f g u : OrdinalExpression (σ :: Γ)} :
      0 < i → ordinalHeadFree (.emul f g) = false → FirstFree Γ σ (i + 1) f j u →
        FirstFree Γ σ i (.emul f g) j u
  | expTail {i j : Nat} {f g u : OrdinalExpression (σ :: Γ)} :
      0 < i → ordinalHeadFree (.emul f g) = false → FirstFree Γ σ i g j u →
        FirstFree Γ σ i (.emul f g) j u
  | collapseHead {j : Nat} {f g u : OrdinalExpression (σ :: Γ)} :
      ordinalHeadFree (.collapse f g) = false → FirstFree Γ σ 1 f j u →
        FirstFree Γ σ 0 (.collapse f g) j u
  | collapseTail {j : Nat} {f g u : OrdinalExpression (σ :: Γ)} :
      ordinalHeadFree (.collapse f g) = false → FirstFree Γ σ 0 g j u →
        FirstFree Γ σ 0 (.collapse f g) j u

end LogicLineages.OrdinalComparison.Source.OriginalDomain
