module
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorDefinitions
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceEraser

def inflated {Γ} (t : OrdinalExpression Γ) : OrdinalExpression Γ :=
  .add (.add (.add t .one) (.add t .one)) t

def eraserVector {Γ} (a b : OrdinalExpression Γ) : OrdinalVector Γ 0 :=
  fun _ => .collapse .one (.add (inflated a) b)

/-- Explicit successful full assignment and finite raw ordinal value, not a fallback scalar. -/
def Scalar (G : Nat → Nat) {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (t : OriginalTerm Γ .ground) (n : Nat) : Prop :=
  ∃ v : OrdinalVector Γ 0,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t=some v ∧
    ParametricSourceSuccessor.denoteWith G ν (v 0)=(n : Ordinal)
end LogicLineages.OrdinalComparison.Source.ParametricSourceEraser
