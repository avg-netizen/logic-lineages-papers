module
public import LogicLineages.OrdinalComparison.ParametricSourceEraserDefinitions
public import LogicLineages.OrdinalComparison.SourceGroundEquivalenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricLiteralWeakWrapper
def three {Γ : List Ty} : OrdinalExpression Γ := .add (.add .one .one) .one
def five {Γ : List Ty} : OrdinalExpression Γ :=
  .add (.add (.add .one .one) (.add .one .one)) .one
def identityApply {Γ} (t : OriginalTerm Γ .ground) : OriginalTerm Γ .ground :=
  .app GroundEquivalence.identity t
def constantApply {Γ} (t : OriginalTerm Γ .ground) : OriginalTerm Γ .ground :=
  .app GroundEquivalence.constant t
end LogicLineages.OrdinalComparison.Source.ParametricLiteralWeakWrapper
