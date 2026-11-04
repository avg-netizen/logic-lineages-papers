module
public import LogicLineages.OrdinalComparison.SourceGammaCollisionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaCollision.Targets
open SourceCollisionCompletion ParametricSourceEraser

def ActualControlGap : Prop := ∀ b : Nat,
  (∀ n : Nat,g b n=SourceMachineControlNonperiodicity.gamma b (n+2)+1) ∧
  StrictMono (g b) ∧ (∀ n : Nat,0<g b n) ∧ (∀ n : Nat,4*g b n<g b (n+1))

def NumericCollision : Prop := ∀ b p q : Nat,
  rightValue b p q ≤ leftValue b p q ∧
  (leftValue b p q=rightValue b p q ↔ p=q) ∧
  (p≠q → 2 ≤ leftValue b p q-rightValue b p q)

def ActualSourceCollision : Prop := ∀ (b : Nat) (Γ : List Ty)
    (ν : OrdinalComponent Γ → Ordinal) (p q : OriginalTerm Γ .ground) (x y : Nat),
  Scalar (SourceMachineControlNonperiodicity.gamma b) ν p x →
  Scalar (SourceMachineControlNonperiodicity.gamma b) ν q y →
    Scalar (SourceMachineControlNonperiodicity.gamma b) ν (detectorLeft p q) (leftValue b x y) ∧
    Scalar (SourceMachineControlNonperiodicity.gamma b) ν (detectorRight p q) (rightValue b x y) ∧
    (∀ l r : Nat,
      Scalar (SourceMachineControlNonperiodicity.gamma b) ν (detectorLeft p q) l →
      Scalar (SourceMachineControlNonperiodicity.gamma b) ν (detectorRight p q) r →
      r ≤ l ∧ (l=r ↔ x=y) ∧ (x≠y → 2 ≤ l-r))
end LogicLineages.OrdinalComparison.Source.SourceGammaCollision.Targets
