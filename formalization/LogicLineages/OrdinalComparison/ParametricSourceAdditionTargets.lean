module
public import LogicLineages.OrdinalComparison.ParametricSourceAdditionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceAddition.Targets
open SourceAdditionCompletion SourceSortCompletion

def AtomicAssignmentValue : Prop := ∀ G : Nat → Nat, StrictMono G → (∀ n : Nat,n ≤ G n) →
  ∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (a b : Atom Γ),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (eraser a b) = some (eraserVector a b) ∧
    ParametricSourceSuccessor.denoteWith G (fun c => ((ρ c+1 : Nat) : Ordinal)) (eraserVector a b 0) =
      ((G (3*atomValue ρ a+atomValue ρ b+8)+1 : Nat) : Ordinal)

def WeightedEquality : Prop := ∀ G : Nat → Nat, StrictMono G → (∀ n : Nat,n ≤ G n) →
  ∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (a b c d : Atom Γ),
    Equation G ρ (eraser a b) (eraser c d) ↔
      3*atomValue ρ a+atomValue ρ b = 3*atomValue ρ c+atomValue ρ d

def ExactAddition : Prop := ∀ G : Nat → Nat, StrictMono G → (∀ n : Nat,n ≤ G n) →
  ∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (a b c : Variable Γ .ground),
    (∀ d : Nat, AddWitness G ρ a b c d ↔ input ρ a+input ρ b=input ρ c ∧ d=3*input ρ b) ∧
    (AddFormula G ρ a b c ↔ input ρ a+input ρ b=input ρ c)

def ActualGammaAddition : Prop := ∀ (b : Nat) (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat)
    (x y z : Variable Γ .ground),
  (∀ d : Nat, AddWitness (SourceMachineControlNonperiodicity.gamma b) ρ x y z d ↔
    input ρ x+input ρ y=input ρ z ∧ d=3*input ρ y) ∧
  (AddFormula (SourceMachineControlNonperiodicity.gamma b) ρ x y z ↔ input ρ x+input ρ y=input ρ z)
end LogicLineages.OrdinalComparison.Source.ParametricSourceAddition.Targets
