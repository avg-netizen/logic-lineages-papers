module
public import LogicLineages.OrdinalComparison.ParametricCanonicalObservationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricCanonicalObservation.Targets

def OmegaFreeTransport : Prop := ∀ (G : Nat → Nat) (c : Ordinal.{0} → Nat),
  ParametricActualCollapse.Equation G c → ∀ (ι : Type)
    (ν : ι → Ordinal.{0}) (t : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι),
  (∀ i, ∃ n : Nat, ν i=(n : Ordinal)) → SourceRestrictedAssignmentFinite.OmegaFree t →
    denoteUsing c ν t=ParametricSourceSuccessor.denoteWith G ν t

def ActualAssignmentTransport : Prop := ∀ (G : Nat → Nat) (c : Ordinal.{0} → Nat),
  ParametricActualCollapse.Equation G c → ∀ (Γ : List Ty) (τ : Ty)
    (t : OriginalTerm Γ τ) (ν : OrdinalComponent Γ → Nat),
  SourceMachineRawValuations.AllGround Γ → SourceGroundBinderFragment.Fragment t →
  ∃ v : OrdinalVector Γ τ.level,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t=some v ∧
    ∀ j, denoteUsing c (fun k => (ν k : Ordinal)) (v j)=
      ParametricSourceSuccessor.denoteWith G (fun k => (ν k : Ordinal)) (v j)

def ScalarEquivalence : Prop := ∀ (G : Nat → Nat) (c : Ordinal.{0} → Nat),
  ParametricActualCollapse.Equation G c → ∀ (Γ : List Ty)
    (t : OriginalTerm Γ .ground) (ν : OrdinalComponent Γ → Nat),
  SourceMachineRawValuations.AllGround Γ → SourceGroundBinderFragment.Fragment t →
  ∀ n : Nat, ScalarUsing c (fun k => (ν k : Ordinal)) t n ↔
    ParametricSourceEraser.Scalar G (fun k => (ν k : Ordinal)) t n
end LogicLineages.OrdinalComparison.Source.ParametricCanonicalObservation.Targets
