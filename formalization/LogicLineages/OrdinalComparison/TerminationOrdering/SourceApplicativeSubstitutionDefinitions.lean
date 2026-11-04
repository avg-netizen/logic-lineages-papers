module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSubstitutionEnvironmentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConditionalLambdaSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceBottomSpineComputabilityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceApplicativeSubstitution
open Source NumberedRewriteSyntax
/-- Literal variable/bottom/application fragment; no binders or headed constructors. -/
def ApplicativeFragment {Symbol : Type} {arity : Symbol → Nat} :
    {Gamma : List Ty} → {tau : Ty} → AuxTerm Symbol arity Gamma tau → Prop
  | _, _, .var _ => True
  | _, _, .bottom _ => True
  | _, _, .app f a => ApplicativeFragment f ∧ ApplicativeFragment a
  | _, _, _ => False
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceApplicativeSubstitution
