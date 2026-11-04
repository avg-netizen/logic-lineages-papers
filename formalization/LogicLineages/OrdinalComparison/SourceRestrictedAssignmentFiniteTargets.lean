module
public import LogicLineages.OrdinalComparison.SourceRestrictedAssignmentFiniteDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceRestrictedAssignmentFinite.Targets
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def FiniteDenotation : Prop := ∀ (ι : Type) (G : Nat → Nat)
    (ν : ι → Ordinal.{0}) (t : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι),
  (∀ i, ∃ n : Nat, ν i=(n : Ordinal)) → OmegaFree t →
    ∃ n : Nat, ParametricSourceSuccessor.denoteWith G ν t=(n : Ordinal)

def ActualAssignment : Prop := ∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ),
  SourceMachineRawValuations.AllGround Γ → SourceGroundBinderFragment.Fragment t →
    ∃ v : OrdinalVector Γ τ.level,
      AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t=some v ∧
      ∀ j, OmegaFree (v j)

def FiniteScalar : Prop := ∀ (G : Nat → Nat) (Γ : List Ty)
    (t : OriginalTerm Γ .ground) (ν : OrdinalComponent Γ → Nat),
  SourceMachineRawValuations.AllGround Γ → SourceGroundBinderFragment.Fragment t →
    ∃ n : Nat, ParametricSourceEraser.Scalar G (fun c => (ν c : Ordinal)) t n
end LogicLineages.OrdinalComparison.Source.SourceRestrictedAssignmentFinite.Targets
