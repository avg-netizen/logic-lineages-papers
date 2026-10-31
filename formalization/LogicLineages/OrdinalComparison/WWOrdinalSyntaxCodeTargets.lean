module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OrdinalSyntax

def OrdinalSyntaxFoldCorrect : Prop :=
  ∀ (ι α : Type) (index : ι → Nat) (leaf : Nat → α) (branch : Nat → α → α → α)
    (t : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι),
    fold leaf branch (code index t) = termFold index leaf branch t

def OrdinalSyntaxFoldPrimitiveRecursive : Prop :=
  ∀ (α : Type) [Primcodable α] (leaf : Nat → α) (branch : Nat → α → α → α),
    Primrec leaf → Primrec (fun p : Nat × α × α => branch p.1 p.2.1 p.2.2) →
      Primrec (fold leaf branch)
end LogicLineages.OrdinalComparison.Source.Targets
