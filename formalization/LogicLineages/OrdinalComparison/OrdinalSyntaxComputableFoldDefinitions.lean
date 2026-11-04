module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntaxComputableFold
def atom (n : Nat) : Prop := n%8<4 ∨ n%8=7
instance (n : Nat) : Decidable (atom n) := inferInstanceAs (Decidable (_ ∨ _))
def indexedFold {P A : Type} (leaf : P × Nat → A)
    (branch : P × (Nat × A × A) → A) (p : P) (n : Nat) : A :=
  OrdinalSyntax.fold (fun k => leaf (p,k)) (fun k a b => branch (p,k,a,b)) n
end LogicLineages.OrdinalComparison.Source.OrdinalSyntaxComputableFold
