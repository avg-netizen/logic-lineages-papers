module
public import LogicLineages.OrdinalComparison.TrackedSourceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.TrackedSource.Targets
open SourceFreeOccurrences AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def ExactGrammar : Prop := ∀ (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1)))
    (n : Nat) (t : OriginalTerm Γ (Ty.curriedGround n)),
  Generated k F t ↔ ∃e : Expr k Γ F n,erase e=t

def ExactOccurrences : Prop := ∀ (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1)))
    (n : Nat) (e : Expr k Γ F n),freeOccurrences (erase e)=occurrences e

def ExactActivity : Prop := ∀ (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1)))
    (n : Nat) (e : Expr k Γ F n),
  active e=true ↔ (⟨Ty.curriedGround (k+1),F⟩ : PackedVariable Γ) ∈ freeOccurrences (erase e)

def ActualAssignment : Prop := ∀ (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1)))
    (n : Nat) (e : Expr k Γ F n),
  ∃v,assignment OrdinalSyntax.defaultPolicy (erase e)=some v ∧
    ∀j,GeneratedOrdinalGrade Γ j.val (v j)
end LogicLineages.OrdinalComparison.Source.TrackedSource.Targets
