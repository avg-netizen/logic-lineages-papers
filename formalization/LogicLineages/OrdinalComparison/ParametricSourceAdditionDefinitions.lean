module
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorDefinitions
public import LogicLineages.OrdinalComparison.SourceAdditionCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceAddition
open SourceAdditionCompletion SourceSortCompletion

def atomExpression {Γ} : Atom Γ → OrdinalExpression Γ
  | .zero => .one
  | .var x => .var ⟨.ground,x,0⟩
def atomValue {Γ} (ρ : OrdinalComponent Γ → Nat) : Atom Γ → Nat
  | .zero => 0
  | .var x => input ρ x
def eraserVector {Γ} (a b : Atom Γ) : OrdinalVector Γ 0 := fun _ =>
  .collapse .one (.add
    (.add (.add (.add (atomExpression a) .one) (.add (atomExpression a) .one))
      (atomExpression a)) (atomExpression b))

def Equation (G : Nat → Nat) {Γ} (ρ : OrdinalComponent Γ → Nat)
    (a b : OriginalTerm Γ .ground) : Prop :=
  ∃ va vb : OrdinalVector Γ 0,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a = some va ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b = some vb ∧
    ParametricSourceSuccessor.denoteWith G (fun c => ((ρ c+1 : Nat) : Ordinal)) (va 0) =
      ParametricSourceSuccessor.denoteWith G (fun c => ((ρ c+1 : Nat) : Ordinal)) (vb 0)

def AddWitness (G : Nat → Nat) {Γ} (ρ : OrdinalComponent Γ → Nat)
    (a b c : Variable Γ .ground) (d : Nat) : Prop :=
  Equation G (extend ρ d) (eraser (.var (.there b)) .zero) (eraser .zero (.var .here)) ∧
  Equation G (extend ρ d) (eraser (.var (.there a)) (.var .here)) (eraser (.var (.there c)) .zero)
def AddFormula (G : Nat → Nat) {Γ} (ρ : OrdinalComponent Γ → Nat)
    (a b c : Variable Γ .ground) : Prop := ∃ d, AddWitness G ρ a b c d
end LogicLineages.OrdinalComparison.Source.ParametricSourceAddition
