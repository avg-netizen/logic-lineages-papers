module
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceSuccessor.Targets
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def PhiCalibration : Prop :=
  (∀ (G : Nat → Nat) (a : Ordinal.{0}), ¬ a < epsilonZero → ParametricActualCollapse.collapseWith G a = 0) ∧
  (∀ a : Ordinal.{0}, ParametricActualCollapse.collapseWith Phi a = actualCollapse a) ∧
  ∀ (ι : Type) (ρ : ι → Ordinal.{0}) (t : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι),
    denoteWith Phi ρ t = denote ρ t

def ExactSubstitution : Prop := ∀ (ι κ : Type) (G : Nat → Nat)
    (ρ : κ → Ordinal.{0})
    (σ : ι → LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term κ)
    (t : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι),
  denoteWith G ρ (substitute σ t) = denoteWith G (fun i => denoteWith G ρ (σ i)) t

def GenericSourceGraph : Prop := ∀ G : Nat → Nat, StrictMono G → (∀ n : Nat,n ≤ G n) →
  ∀ (Γ : List Ty) (x : Variable Γ .ground),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (successorProbe x) =
      some (fun _ => .collapse .one (.add .one (.var ⟨.ground,x,0⟩))) ∧
    ∀ (ρ : OrdinalComponent Γ → Nat) (y : Nat),
      Observation G ρ (successorProbe x) y ↔ y = G (ρ ⟨.ground,x,0⟩+4)

def ActualGammaGraph : Prop := ∀ (b : Nat) (Γ : List Ty)
    (x : Variable Γ .ground) (ρ : OrdinalComponent Γ → Nat) (y : Nat),
  Observation (SourceMachineControlNonperiodicity.gamma b) ρ (successorProbe x) y ↔
    y = SourceMachineControlNonperiodicity.gamma b (ρ ⟨.ground,x,0⟩+4)
end LogicLineages.OrdinalComparison.Source.ParametricSourceSuccessor.Targets
