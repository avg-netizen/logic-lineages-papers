module
public import LogicLineages.OrdinalComparison.ParametricCoefficientOneDefinitions
public import LogicLineages.OrdinalComparison.SourceSortCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceSuccessor
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Existing literal ordinal-term syntax, separately interpreted at G.
Only the collapse function changes; no source or assignment constructor changes. -/
noncomputable def denoteWith {ι : Type} (G : Nat → Nat) (ρ : ι → Ordinal.{0}) :
    LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι → Ordinal.{0}
  | .var i => ρ i
  | .zero => 0
  | .one => 1
  | .omega => Ordinal.omega0
  | .add a b => ordinalNaturalSum (denoteWith G ρ a) (denoteWith G ρ b)
  | .emul a b => ordinalNaturalProduct ((2 : Ordinal)^denoteWith G ρ a) (denoteWith G ρ b)
  | .collapse a b => (ParametricActualCollapse.collapseWith G
      (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 (denoteWith G ρ a))
        (denoteWith G ρ b)) : Ordinal)

/-- Same full default-policy assignment and positive raw input convention. -/
def Observation (G : Nat → Nat) {Γ : List Ty} (ρ : OrdinalComponent Γ → Nat)
    (t : OriginalTerm Γ .ground) (y : Nat) : Prop :=
  ∃ v : OrdinalVector Γ 0,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v ∧
    denoteWith G (fun c => ((ρ c+1 : Nat) : Ordinal)) (v 0) = ((y+1 : Nat) : Ordinal)
end LogicLineages.OrdinalComparison.Source.ParametricSourceSuccessor
