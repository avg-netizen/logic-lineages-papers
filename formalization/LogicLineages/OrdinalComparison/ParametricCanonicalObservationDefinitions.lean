module
public import LogicLineages.OrdinalComparison.SourceRestrictedAssignmentFiniteDefinitions
public import LogicLineages.OrdinalComparison.ParametricActualCollapseDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricCanonicalObservation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

noncomputable def denoteUsing {ι : Type} (c : Ordinal.{0} → Nat) (ν : ι → Ordinal.{0}) :
    LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι → Ordinal.{0}
  | .var i => ν i
  | .zero => 0
  | .one => 1
  | .omega => Ordinal.omega0
  | .add a b => ordinalNaturalSum (denoteUsing c ν a) (denoteUsing c ν b)
  | .emul a b => ordinalNaturalProduct ((2 : Ordinal)^denoteUsing c ν a) (denoteUsing c ν b)
  | .collapse a b => (c (ordinalNaturalSum
      (ordinalNaturalProduct Ordinal.omega0 (denoteUsing c ν a)) (denoteUsing c ν b)) : Ordinal)

def ScalarUsing (c : Ordinal.{0} → Nat) {Γ : List Ty}
    (ν : OrdinalComponent Γ → Ordinal) (t : OriginalTerm Γ .ground) (n : Nat) : Prop :=
  ∃ v : OrdinalVector Γ 0,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t=some v ∧
    denoteUsing c ν (v 0)=(n : Ordinal)
end LogicLineages.OrdinalComparison.Source.ParametricCanonicalObservation
