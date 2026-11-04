module
public import LogicLineages.OrdinalComparison.SourceGammaCollisionDefinitions
public import LogicLineages.OrdinalComparison.ParametricSourceAdditionDefinitions
public import LogicLineages.OrdinalComparison.SourceAggregateCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaAggregate
open ParametricSourceEraser ParametricSourceSuccessor

def Equal (G : Nat → Nat) {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (p q : OriginalTerm Γ .ground) : Prop :=
  ∃ vp vq : OrdinalVector Γ 0,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy p=some vp ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy q=some vq ∧
    denoteWith G ν (vp 0)=denoteWith G ν (vq 0)
def FiniteLeaves (b : Nat) {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)) : Prop :=
  ∀ e ∈ es,∃ x y : Nat,
    Scalar (SourceMachineControlNonperiodicity.gamma b) ν e.1 x ∧
    Scalar (SourceMachineControlNonperiodicity.gamma b) ν e.2 y
def AllEqual (b : Nat) {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)) : Prop :=
  ∀ e ∈ es,Equal (SourceMachineControlNonperiodicity.gamma b) ν e.1 e.2
end LogicLineages.OrdinalComparison.Source.SourceGammaAggregate
