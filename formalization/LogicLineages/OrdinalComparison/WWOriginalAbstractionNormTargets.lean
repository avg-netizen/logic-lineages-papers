module
public import LogicLineages.OrdinalComparison.WWOriginalBoundedDeltaDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain AdmissibleSum

/-- Head-one closure transports the original bounded norm via an actual
admissible extension, without a fresh inequality hypothesis. -/
def OriginalHeadClosureVectorBounded : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (h : OrdinalVector (σ :: Γ) m),
    BoundedVector h → BoundedVector (fun j => ordinalHeadClosure (h j))

/-- Actual source lambda-abstraction supplier: delta plus retained actual
head-closed input coordinates. This is not a box/application result and does
not by itself complete the original whole-assignment F1 claim. -/
def OriginalSourceAbstractionBounded : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (p : Policy) (h : OrdinalVector (σ :: Γ) m),
    (∀ i, HeadGrade Γ σ i.val (h i)) → SourceBoundedVector h →
    ∃ v : OrdinalVector Γ (max (σ.level + 1) m),
      AdmissibleAssignment.abstraction p h = some v ∧
      (∀ j, AmbientGrade Γ j.val (v j)) ∧ SourceBoundedVector v

end LogicLineages.OrdinalComparison.Source.Targets
