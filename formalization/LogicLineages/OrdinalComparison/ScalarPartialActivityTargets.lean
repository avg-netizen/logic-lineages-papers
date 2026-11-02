module
public import LogicLineages.OrdinalComparison.ScalarPartialActivityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ScalarPartialActivity.Targets
open SourceFreeOccurrences AdmissibleAssignment AssignmentSupport

def ExactScalarOldNames : Prop := ∀ (Γ : List Ty) (σ : Ty) (p : AdmissibleSum.Policy)
    (t : OrdinalExpression (σ :: Γ)) (v : OrdinalPartialVector Γ σ),
  AdmissiblePartial.run p 0 t=some v → ∀x : PackedVariable Γ,x∈names (v 0) ↔ x∈oldNames t

/-- Both actual assignment and scalar partial success are derived, not supplied.
Arbitrary original internal syntax is retained under the ground binder. -/
def FullGroundSourceTransport : Prop := ∀ (Γ : List Ty) (τ : Ty) (p : AdmissibleSum.Policy)
    (t : OriginalTerm (.ground :: Γ) τ),∃h v,
  assignment p t=some h ∧ AdmissiblePartial.run p 0 (h 0)=some v ∧
  (∀j,GeneratedOrdinalGrade Γ j.val (v j)) ∧
  ∀ (σ : Ty) (x : Variable Γ σ),
    (⟨σ,x⟩ : PackedVariable Γ)∈names (v 0) ↔
      (⟨σ,Variable.there x⟩ : PackedVariable (.ground :: Γ))∈freeOccurrences t

def ActualTrackedActivity : Prop := ∀ (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1)))
    (n : Nat) (e : TrackedSource.Expr k (.ground :: Γ) (.there F) n),∃h v,
  assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e)=some h ∧
  AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (h 0)=some v ∧
    (TrackedSource.active e=true ↔ (⟨Ty.curriedGround (k+1),F⟩ : PackedVariable Γ)∈names (v 0))
end LogicLineages.OrdinalComparison.Source.ScalarPartialActivity.Targets
