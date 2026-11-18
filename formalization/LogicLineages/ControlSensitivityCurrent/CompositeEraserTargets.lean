module
public import LogicLineages.ControlSensitivityCurrent.CompositeEraserDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CompositeEraserTargets
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open CompositeEraser
/-- Actual composite-source closure, arbitrary policy, no atomic restriction. -/
def AssignmentClosure : Prop := ∀ (p : AdmissibleSum.Policy) (Γ : List Ty)
  (a b : OriginalTerm Γ .ground) (va vb : OrdinalVector Γ 0),
  AdmissibleAssignment.assignment p a = some va →
  AdmissibleAssignment.assignment p b = some vb →
  AdmissibleAssignment.assignment p (SourceCollisionCompletion.eraser a b) =
    some (ParametricSourceEraser.eraserVector (va 0) (vb 0))

def ScalarUniqueness : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat)
  (Γ : List Ty) (ν : OrdinalComponent Γ → Ordinal) (t : OriginalTerm Γ .ground) (x y : Nat),
  Scalar p f ν t x → Scalar p f ν t y → x = y

/-- Conditional finite closure only; full source collision must prove input totality separately. -/
def FiniteClosure : Prop := ∀ (p : AdmissibleSum.Policy) (f : Nat → Nat),
  StrictMono f → (∀ n : Nat, n ≤ f n) → ∀ (Γ : List Ty)
  (ν : OrdinalComponent Γ → Ordinal) (a b : OriginalTerm Γ .ground) (x y : Nat),
  Scalar p f ν a x → Scalar p f ν b y →
  Scalar p f ν (SourceCollisionCompletion.eraser a b) (f (3*x+y+4)+1) ∧
  ∀ z : Nat, Scalar p f ν (SourceCollisionCompletion.eraser a b) z ↔ z = f (3*x+y+4)+1
end LogicLineages.ControlSensitivityCurrent.CompositeEraserTargets
