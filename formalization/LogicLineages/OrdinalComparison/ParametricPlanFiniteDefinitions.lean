module
public import LogicLineages.OrdinalComparison.ParametricPrimitiveFiniteDefinitions
public import LogicLineages.OrdinalComparison.SourceGammaAggregateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPlanFinite
open ExistentialPlan GroundEquivalence ParametricSourceEraser ParametricPrimitiveFinite

def LeafFinite (G : Nat → Nat) {Γ} (a b : Input Γ .ground) : Prop :=
  ∀ ρ : Variable Γ .ground → Nat, ∃ x y : Nat,
    Scalar G (positive (inputs ρ)) a.term x ∧ Scalar G (positive (inputs ρ)) b.term y

/-- Uniform conditions only on supplied source leaves, not gate truth. -/
def UniformFinite (G : Nat → Nat) : {Γ : List Ty} → Plan Γ → Prop
  | _,.done => True
  | _,.equation a b q => LeafFinite G a b ∧ UniformFinite G q
  | _,.gate _ q => UniformFinite G q
  | _,.existsGround q => UniformFinite G q

def ForestFinite (G : Nat → Nat) {Γ} (ρ : Variable Γ .ground → Nat)
    (es : List (Input Γ .ground × Input Γ .ground)) : Prop :=
  ∀ e ∈ es, ∃ x y : Nat,
    Scalar G (positive (inputs ρ)) e.1.term x ∧ Scalar G (positive (inputs ρ)) e.2.term y
end LogicLineages.OrdinalComparison.Source.ParametricPlanFinite
