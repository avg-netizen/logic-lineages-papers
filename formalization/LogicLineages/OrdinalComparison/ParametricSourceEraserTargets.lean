module
public import LogicLineages.OrdinalComparison.ParametricSourceEraserDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceEraser.Targets
open SourceCollisionCompletion ParametricSourceSuccessor

def FullAssignmentClosure : Prop := ∀ (Γ : List Ty) (p q : OriginalTerm Γ .ground)
    (vp vq : OrdinalVector Γ 0),
  AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy p=some vp →
  AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy q=some vq →
  AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (eraser p q)=
    some (eraserVector (vp 0) (vq 0))

def GenericFiniteClosure : Prop := ∀ G : Nat → Nat, StrictMono G → (∀ n : Nat,n ≤ G n) →
  ∀ (Γ : List Ty) (ν : OrdinalComponent Γ → Ordinal) (p q : OriginalTerm Γ .ground) (x y : Nat),
    Scalar G ν p x → Scalar G ν q y →
    (Scalar G ν (eraser p q) (G (3*x+y+4)+1) ∧
      ∀ z : Nat, Scalar G ν (eraser p q) z ↔ z=G (3*x+y+4)+1)

def NaturalObservationClosure : Prop := ∀ G : Nat → Nat, StrictMono G → (∀ n : Nat,n ≤ G n) →
  ∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (p q : OriginalTerm Γ .ground) (x y : Nat),
    Observation G ρ p x → Observation G ρ q y → ∀ z : Nat,
      Observation G ρ (eraser p q) z ↔ z=G (3*x+y+8)

def ActualGammaClosure : Prop := ∀ b : Nat,
  (∀ (Γ : List Ty) (ν : OrdinalComponent Γ → Ordinal) (p q : OriginalTerm Γ .ground) (x y : Nat),
    Scalar (SourceMachineControlNonperiodicity.gamma b) ν p x →
    Scalar (SourceMachineControlNonperiodicity.gamma b) ν q y → ∀ z : Nat,
      Scalar (SourceMachineControlNonperiodicity.gamma b) ν (eraser p q) z ↔
        z=SourceMachineControlNonperiodicity.gamma b (3*x+y+4)+1) ∧
  (∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Nat) (p q : OriginalTerm Γ .ground) (x y : Nat),
    Observation (SourceMachineControlNonperiodicity.gamma b) ρ p x →
    Observation (SourceMachineControlNonperiodicity.gamma b) ρ q y → ∀ z : Nat,
      Observation (SourceMachineControlNonperiodicity.gamma b) ρ (eraser p q) z ↔
        z=SourceMachineControlNonperiodicity.gamma b (3*x+y+8))
end LogicLineages.OrdinalComparison.Source.ParametricSourceEraser.Targets
