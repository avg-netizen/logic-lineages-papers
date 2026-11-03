module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompilerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariables
open BalancedSyntax

abbrev Input := BalancedRawCompiler.Input
abbrev Code := BalancedRawCompiler.Code

/-- The ORIGINAL pair support at EVERY source shape, before cancellation or
sign filtering. Only duplicate raw names are removed. The original common
certificate and its possibly repeated/dependent basis entries are unchanged. -/
def sourceSupport (Γ : List Nat) (C : Certificate Γ) (E F : Syntax Γ) : List Nat :=
  (rawVariables Γ C E ++ rawVariables Γ C F).dedup

/-- Literal finite conjunction of x=x in the EXISTING ordinary BASE syntax.
The empty conjunction is truth. No new variable, predicate or independent
basis valuation is introduced. -/
def variablesFormula (support : List Nat) : BaseFormula.Formula :=
  BalancedBoxFormula.conjunction
    (support.map (fun i => .equal (.variable i) (.variable i)))

/-- The unchanged accepted typed comparison FIRST, tautological original
support padding SECOND. No simplification or cancellation removes the padding,
including when the requested sign is impossible or the comparison is constant. -/
noncomputable def sourceFormula (Γ : List Nat) (C : Certificate Γ)
    (E F : Syntax Γ) (desired : Int) : BaseFormula.Formula :=
  .conjunction (BalancedTypedCompiler.typedFormula Γ C E F desired)
    (variablesFormula (sourceSupport Γ C E F))

/-- All-shape raw extraction uses the EXISTING codeVariables algorithm.
Unlike BalancedBoxFormula.rawSupport, this interface also accepts shape [].
The underlying decoders and malformed-input defaults are not changed. -/
def rawSupport (Γ : List Nat) (C E F : Nat) : List Nat :=
  (BalancedEvaluation.codeVariables Γ C E ++
    BalancedEvaluation.codeVariables Γ C F).dedup

/-- Literal existing equality instructions with ACTUAL BaseTerm variable
codes 4*i+1, folded with existing conjunction and the true empty tail. -/
def variablesCode (support : List Nat) : Code :=
  CommonHeadCode.conjoin
    (support.map (fun i => [(2, 4 * i + 1, 4 * i + 1)]))

/-- The ORIGINAL raw compiler output FIRST, literal padding code SECOND.
The accepted compiler, its recursive calls, original thresholds, point boxes,
guards and all raw defaults are preserved without modification. -/
noncomputable def formulaCode (Γ : List Nat) (C E F : Nat)
    (desired : Int) : Code :=
  CommonHeadCode.conjunction (BalancedRawCompiler.compileCode Γ C E F desired)
    (variablesCode (rawSupport Γ C E F))

/-- Tupled numeric output on the accepted full raw input type. Effectiveness
is Computable on ALL inputs, not primitive recursion of the total compiler. -/
noncomputable def outputCode (a : Input) : Code :=
  formulaCode a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariables
