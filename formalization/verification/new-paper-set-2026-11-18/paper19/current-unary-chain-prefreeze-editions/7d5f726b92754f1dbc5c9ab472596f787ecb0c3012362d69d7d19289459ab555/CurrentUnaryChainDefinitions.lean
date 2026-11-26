module
public import LogicLineages.OrdinalComparison.SourceUnaryChainDefinitions
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentUnaryChain

open LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

abbrev Unary (Γ : List Ty) := OriginalTerm Γ (.arrow .ground .ground)

/-- Every actual unary operand is interpreted under the same selected policy. -/
def Assigned (p : AdmissibleSum.Policy) {Γ} (vs : List (Unary Γ))
    (ws : List (OrdinalVector Γ 1)) : Prop :=
  List.Forall₂ (fun v w => AdmissibleAssignment.assignment p v = some w) vs ws

/-- Exact scalar of the ground chain body; retains both original coordinates
of each weakened operator. No operator gets a new source body or scalar. -/
def scalarSpine {Γ} : List (OrdinalVector Γ 1) → OrdinalExpression (.ground :: Γ)
  | [] => .var ⟨.ground,.here,0⟩
  | v :: vs => .collapse (ordinalExpressionRename (Renaming.weaken Γ .ground) (v 1))
      (.add (ordinalExpressionRename (Renaming.weaken Γ .ground) (v 0)) (scalarSpine vs))

/-- Actual policy association is retained in both literal partial coordinates. -/
def partialSpine (p : AdmissibleSum.Policy) {Γ} :
    List (OrdinalVector Γ 1) → OrdinalPartialVector Γ .ground
  | [] => fun _ => .one
  | v :: vs => fun j =>
    if j.val = 0 then
      .collapse (v 1) (AdmissiblePartial.three p .activeAdd
        (.add (v 0) .one) (partialSpine p vs 0) .one)
    else
      .add (.add (v 1) .one) (AdmissiblePartial.three p .activeAdd
        .one (partialSpine p vs j) .one)

noncomputable def headSum (f : Nat → Nat) {Γ} (ν : OrdinalComponent Γ → Ordinal) :
    List (OrdinalVector Γ 1) → Ordinal
  | [] => 1
  | v :: vs =>
    ordinalNaturalSum (ordinalNaturalSum (ParametricSourceSuccessor.denoteWith f ν (v 1)) 3)
      (headSum f ν vs)

/-- Genuine shared positive ground coordinates, all functional coordinates
observed at the common unit, with no all-one source inhabitant. -/
def commonUnits {Γ} (ρ : Variable Γ .ground → Nat) : OrdinalComponent Γ → Ordinal
  | ⟨.ground,x,_⟩ => ((ρ x+1 : Nat) : Ordinal)
  | ⟨.arrow _ _,_,_⟩ => 1

end LogicLineages.ControlSensitivityCurrent.CurrentUnaryChain
