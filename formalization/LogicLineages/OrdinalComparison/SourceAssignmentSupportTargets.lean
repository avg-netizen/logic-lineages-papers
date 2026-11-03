module
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AssignmentSupport.Targets
open SourceFreeOccurrences AdmissibleAssignment

def ExactHeadClosureNames : Prop := ∀ (Γ : List Ty) (σ : Ty) (t : OrdinalExpression (σ :: Γ)),
  names (ordinalHeadClosure t)=(names t).filterMap dropBound

def ActualPartialSupport : Prop := ∀ (Γ : List Ty) (σ : Ty) (p : AdmissibleSum.Policy)
    (i : Nat) (t : OrdinalExpression (σ :: Γ)) (v : OrdinalPartialVector Γ σ),
  AdmissiblePartial.run p i t=some v → ∀j,Supported ((names t).filterMap dropBound) (v j)

def FullActualAssignmentSupport : Prop := ∀ (Γ : List Ty) (τ : Ty) (p : AdmissibleSum.Policy)
    (t : OriginalTerm Γ τ),∃v,
  assignment p t=some v ∧ (∀j,Supported (freeOccurrences t) (v j)) ∧
    ∀x : PackedVariable Γ,x∈names (v 0) ↔ x∈freeOccurrences t

/-- Opaque syntactic F-freeness pays actual expression F-freeness at every
coordinate. The scalar converse makes the tracked activity test exact. -/
def ActualTrackedInactive : Prop := ∀ (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1)))
    (n : Nat) (e : TrackedSource.Expr k Γ F n),∃v,
  assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e)=some v ∧
    (TrackedSource.active e=false ↔ ∀j,(⟨Ty.curriedGround (k+1),F⟩ : PackedVariable Γ)∉names (v j))
end LogicLineages.OrdinalComparison.Source.AssignmentSupport.Targets
