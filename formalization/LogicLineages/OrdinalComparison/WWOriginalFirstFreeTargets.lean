module
public import LogicLineages.OrdinalComparison.WWOriginalFirstFreeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain

def OriginalFirstFreeEndpoint : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i j : Nat) (t u : OrdinalExpression (σ :: Γ)),
    FirstFree Γ σ i t j u → ordinalHeadFree u = true

def OriginalFirstFreeGrade : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i j : Nat) (t u : OrdinalExpression (σ :: Γ)),
    HeadGrade Γ σ i t → FirstFree Γ σ i t j u → HeadGrade Γ σ j u

/-- Exact repaired wwsc:lem:free. Here n=level(X)+1, so the multiplier is
2^(n-1), not the later larger 2^n. The scalar B is interpreted by its proved
finite value; no output-closure norm or path bound is assumed. -/
def OriginalFirstFreeBound : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (h : OrdinalVector (σ :: Γ) m),
    (∀ i, HeadGrade Γ σ i.val (h i)) → BoundedVector h →
    ∀ (ρ : AdmissibleSubstitution Γ) (i : Fin (m + 1)) (j : Nat)
      (u : OrdinalExpression (σ :: Γ)), FirstFree Γ σ i.val (h i) j u → 0 < j →
      actualOrdinalNorm (expressionValue ρ (ordinalHeadClosure u)) ≤
        2 ^ σ.level * finiteValue (expressionValue ρ (ordinalHeadClosure (h 0)))

end LogicLineages.OrdinalComparison.Source.Targets
