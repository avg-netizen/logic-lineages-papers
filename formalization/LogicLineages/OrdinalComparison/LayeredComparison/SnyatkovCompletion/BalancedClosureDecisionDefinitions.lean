module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariablesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecision
open BalancedSyntax BalancedEvaluation
abbrev Input := BalancedRawCompiler.Input
abbrev Code := BalancedRawCompiler.Code

/-- Positivity on precisely the original pair support. Empty support imposes
no restriction, and all outside raw coordinates remain unrestricted. -/
def positiveFormula (names : List Nat) : BaseFormula.Formula :=
  names.foldr (fun i p => .conjunction (.less (.numeral 0) (.variable i)) p) .truth

def positiveCode (names : List Nat) : Code :=
  CommonHeadCode.conjoin (names.map (fun i => [(3, 0, 4 * i + 1)]))

noncomputable def existsFormula (Γ : List Nat) (C : Certificate Γ)
    (E F : Syntax Γ) (desired : Int) : BaseFormula.Formula :=
  .conjunction (positiveFormula (BalancedExactVariables.sourceSupport Γ C E F))
    (BalancedTypedCompiler.typedFormula Γ C E F desired)

noncomputable def forallFormula (Γ : List Nat) (C : Certificate Γ)
    (E F : Syntax Γ) (desired : Int) : BaseFormula.Formula :=
  .disjunction (.negative (positiveFormula (BalancedExactVariables.sourceSupport Γ C E F)))
    (BalancedTypedCompiler.typedFormula Γ C E F desired)

noncomputable def existsCode (a : Input) : Code :=
  CommonHeadCode.conjunction
    (positiveCode (BalancedExactVariables.rawSupport a.1 a.2.1 a.2.2.1 a.2.2.2.1))
    (BalancedRawCompiler.recursiveCode a)
noncomputable def forallCode (a : Input) : Code :=
  CommonHeadCode.disjunction
    (CommonHeadCode.negative (positiveCode (BalancedExactVariables.rawSupport a.1 a.2.1 a.2.2.1 a.2.2.2.1)))
    (BalancedRawCompiler.recursiveCode a)

noncomputable def existsAnswer (a : Input) : Option Bool :=
  BaseBooleanSource.Code.decideClosureExists (existsCode a)
noncomputable def forallAnswer (a : Input) : Option Bool :=
  BaseBooleanSource.Code.decideClosureForall (forallCode a)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedClosureDecision
