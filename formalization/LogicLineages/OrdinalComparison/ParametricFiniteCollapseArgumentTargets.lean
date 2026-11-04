module
public import LogicLineages.OrdinalComparison.ParametricFiniteCollapseArgumentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricFiniteCollapseArgument.Targets

def MixedArithmetic : Prop :=
  (∀ a : Nat, ordinalNaturalProduct Ordinal.omega0 (a : Ordinal)=Ordinal.omega0*(a : Ordinal)) ∧
  (∀ a b : Nat, ordinalNaturalSum (Ordinal.omega0*(a : Ordinal)) (b : Ordinal)=
    Ordinal.omega0*(a : Ordinal)+(b : Ordinal))

def ExactArgument : Prop := ∀ a b : Nat, argument a b=ParametricFinitePairCollapse.ordinal (a,b)

def DenotationCalibration : Prop := ∀ (ι : Type) (G : Nat → Nat) (ν : ι → Ordinal.{0})
    (s t : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι) (a b : Nat),
  ParametricSourceSuccessor.denoteWith G ν s=(a : Ordinal) →
  ParametricSourceSuccessor.denoteWith G ν t=(b : Ordinal) →
  ParametricSourceSuccessor.denoteWith G ν (.collapse s t)=
    (ParametricFinitePairCollapse.value G (a,b) : Ordinal)
end LogicLineages.OrdinalComparison.Source.ParametricFiniteCollapseArgument.Targets
