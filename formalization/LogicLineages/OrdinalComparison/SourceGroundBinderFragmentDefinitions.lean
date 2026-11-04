module
public import LogicLineages.OrdinalComparison.SourceAggregateCompletionDefinitions
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGroundBinderFragment

/-- Literal syntax restriction only. Free variable types are not restricted here. -/
def Fragment : {Γ : List Ty} → {τ : Ty} → OriginalTerm Γ τ → Prop
  | _,_,.var _ => True
  | _,_,.zeroC => True
  | _,_,.succC => True
  | _,_,.app f a => Fragment f ∧ Fragment a
  | _,_,.lam (σ:=σ) t => σ=Ty.ground ∧ Fragment t
  | _,_,.caseC _ => False
  | _,_,.recC _ => False
  | _,_,.ranked s _ => nomatch s
end LogicLineages.OrdinalComparison.Source.SourceGroundBinderFragment
