module
public import LogicLineages.OrdinalComparison.WWDefaultSyntaxBoxDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OrdinalSyntax

def DefaultSyntaxBoxTailCorrect : Prop :=
  ∀ (Γ : List Ty) (n : Nat) (f g : OrdinalExpression Γ),
    defaultBoxTailCode n (typedCode f) (typedCode g) =
      typedCode (AdmissibleAssignment.boxTail defaultPolicy n f g)

def DefaultSyntaxApplicationCorrect : Prop :=
  ∀ (Γ : List Ty) (σ τ : Ty) (f : OrdinalVector Γ (Ty.arrow σ τ).level)
    (g : OrdinalVector Γ σ.level),
    defaultApplicationCode τ.level σ.level (vectorCode f) (vectorCode g) =
      vectorCode (AdmissibleAssignment.application defaultPolicy f g)

def DefaultSyntaxApplicationPrimitiveRecursive : Prop :=
  Primrec (fun p : Nat × Nat × List Nat × List Nat => defaultApplicationCode p.1 p.2.1 p.2.2.1 p.2.2.2)
end LogicLineages.OrdinalComparison.Source.Targets
