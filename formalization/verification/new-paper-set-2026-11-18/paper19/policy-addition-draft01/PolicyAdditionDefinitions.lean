module
public import LogicLineages.ControlSensitivityCurrent.PolicyGadgetDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyAddition
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open SourceAdditionCompletion SourceSortCompletion
def Equation (p : AdmissibleSum.Policy) (G : Nat → Nat) {Γ} (ρ : OrdinalComponent Γ → Nat)
    (a b : OriginalTerm Γ .ground) : Prop :=
  ∃ va vb : OrdinalVector Γ 0,
    AdmissibleAssignment.assignment p a = some va ∧
    AdmissibleAssignment.assignment p b = some vb ∧
    ParametricSourceSuccessor.denoteWith G (fun c => ((ρ c+1 : Nat) : Ordinal)) (va 0) =
      ParametricSourceSuccessor.denoteWith G (fun c => ((ρ c+1 : Nat) : Ordinal)) (vb 0)

def AddWitness (p : AdmissibleSum.Policy) (G : Nat → Nat) {Γ} (ρ : OrdinalComponent Γ → Nat)
    (a b c : Variable Γ .ground) (d : Nat) : Prop :=
  Equation p G (extend ρ d) (eraser (.var (.there b)) .zero) (eraser .zero (.var .here)) ∧
  Equation p G (extend ρ d) (eraser (.var (.there a)) (.var .here)) (eraser (.var (.there c)) .zero)
def AddFormula (p : AdmissibleSum.Policy) (G : Nat → Nat) {Γ} (ρ : OrdinalComponent Γ → Nat)
    (a b c : Variable Γ .ground) : Prop := ∃ d, AddWitness p G ρ a b c d

def OneFormula (p : AdmissibleSum.Policy) (G : Nat → Nat) (u : Nat) : Prop := ∃ v : Nat,
  Equation p G (extend (singletonVal u) v) (successorProbe .here) (.app identity .zeroC) ∧
  AddFormula p G (extend (singletonVal u) v) (.there .here) (.there .here) .here

def AddValues (p : AdmissibleSum.Policy) (G : Nat → Nat) (a b c : Nat) : Prop :=
  AddFormula p G (tripleVal a b c) .here (.there .here) (.there (.there .here))

def Run (p : AdmissibleSum.Policy) (G : Nat → Nat) : BinaryDAG → Nat → Prop
  | .zero, y => y = 0
  | .one, y => y = 1
  | .double q, y => ∃ x, Run p G q x ∧ AddValues p G x x y
  | .doubleOne q, y => ∃ x z, Run p G q x ∧ AddValues p G x x z ∧ AddValues p G z 1 y
end LogicLineages.ControlSensitivityCurrent.PolicyAddition
