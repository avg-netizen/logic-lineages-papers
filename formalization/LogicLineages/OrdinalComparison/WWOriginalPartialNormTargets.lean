module
public import LogicLineages.OrdinalComparison.WWOriginalFirstFreeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain AdmissibleSum

/-- Compositional supplier only: an explicitly supplied first-free endpoint
budget bounds positive partial outputs. The global theorem below must pay
this premise from original bounded input vectors, not assume it. -/
def OriginalPartialNormFromFreeBudget : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    HeadGrade Γ σ i t → ∀ (ρ : AdmissibleSubstitution Γ) (C : Nat), 0 < C →
    (∀ (k : Nat) (u : OrdinalExpression (σ :: Γ)), FirstFree Γ σ i t k u → 0 < k →
      actualOrdinalNorm (expressionValue ρ (ordinalHeadClosure u)) ≤ C) →
    ∀ v : OrdinalPartialVector Γ σ, AdmissiblePartial.run p i t = some v →
      ∀ j, 0 < j.val → actualOrdinalNorm (expressionValue ρ (v j)) ≤ ordinalPartialSize t * (2 * C)

/-- Actual positive partial bound used by wwsc:thm:norm. The scalar output w
is constrained by the actual root partial equation. All endpoint budgets are
proved from bounded original input, with the unchanged factor2^n. -/
def OriginalVectorPartialNorm : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (p : Policy) (h : OrdinalVector (σ :: Γ) m),
    (∀ i, HeadGrade Γ σ i.val (h i)) → BoundedVector h →
    ∀ (ρ : AdmissibleSubstitution Γ) (w : OrdinalPartialVector Γ σ),
      AdmissiblePartial.run p 0 (h 0) = some w →
      ∀ (i : Fin (m + 1)) (v : OrdinalPartialVector Γ σ),
        AdmissiblePartial.run p i.val (h i) = some v →
        ∀ j, 0 < j.val → actualOrdinalNorm (expressionValue ρ (v j)) ≤
          ordinalPartialSize (h i) *
            (2 ^ (σ.level + 1) * finiteValue (expressionValue ρ (w 0)))

end LogicLineages.OrdinalComparison.Source.Targets
