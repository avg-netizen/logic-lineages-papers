module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxBoxDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OrdinalSyntax

def OrdinalSyntaxBoxPositiveCorrect : Prop :=
  ∀ (Γ : List Ty) (m n : Nat) (f : OrdinalVector Γ m) (g : OrdinalVector Γ n) (i : Nat),
    boxPositive n (vectorCode f) (vectorCode g) i =
      typedCode (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) i)

def OrdinalSyntaxApplicationCorrect : Prop :=
  ∀ (Γ : List Ty) (σ τ : Ty) (f : OrdinalVector Γ (Ty.arrow σ τ).level)
    (g : OrdinalVector Γ σ.level),
    applicationCode τ.level σ.level (vectorCode f) (vectorCode g) =
      vectorCode (AdmissibleAssignment.application allLeftPolicy f g)

def OrdinalSyntaxBoxOperationsPrimitiveRecursive : Prop :=
  Primrec (fun p : Nat × List Nat × List Nat × Nat => boxPositive p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat × Nat × List Nat × List Nat => applicationCode p.1 p.2.1 p.2.2.1 p.2.2.2)
end LogicLineages.OrdinalComparison.Source.Targets
