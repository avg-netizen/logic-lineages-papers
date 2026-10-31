module
public import LogicLineages.OrdinalComparison.WWOriginalBoundedDeltaDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain AdmissibleSum

def OriginalBoundedVectorSupportBridge : Prop :=
  ∀ (Γ : List Ty) (m : Nat) (h : OrdinalVector Γ m), BoundedVector h ↔ SourceBoundedVector h

/-- Whole repaired wwsc:thm:norm. The actual delta definition retains the
original multiplier2^(level(X)+1)*sum(partialSize). Original C^X input and
occurring-vector bounded substitutions are retained verbatim; no free-subtree,
positive-partial, scalar weakness or product/exponential estimate is assumed. -/
def OriginalDeltaPreservesBoundedNorm : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (p : Policy) (h : OrdinalVector (σ :: Γ) m),
    (∀ i, HeadGrade Γ σ i.val (h i)) → SourceBoundedVector h →
    ∃ v : OrdinalVector Γ (max (σ.level + 1) m), delta p h = some v ∧
      (∀ j, AmbientGrade Γ j.val (v j)) ∧ SourceBoundedVector v

end LogicLineages.OrdinalComparison.Source.Targets
