module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparisonDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariablesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariables
open CommonLayerSyntax CommonLayerComparison

abbrev Input := List Nat × Nat × Nat × Int
abbrev Code := List CommonHeadCompiler.Instruction

/-- The original common-layer input support, before cancellation or sign filtering.
Only duplicate names are removed; malformed raw inputs retain the existing decoder. -/
def support (heads : List Nat) (E F : Nat) : List Nat :=
  (codedVariables heads.length E ++ codedVariables heads.length F).dedup

/-- The original compiler followed by literal reflexive equalities in the SAME BASE
syntax. There are no extra names or predicates, including for empty support. -/
noncomputable def formula (heads : List Nat) (E F : Nat) (desired : Int) : BaseFormula.Formula :=
  .conjunction (compile heads E F desired)
    (BalancedExactVariables.variablesFormula (support heads E F))

/-- Literal existing instruction concatenation, not a semantic oracle encoding. -/
noncomputable def output (p : Input) : Code :=
  CommonHeadCode.conjunction (compileCode p.1 p.2.1 p.2.2.1 p.2.2.2)
    (BalancedExactVariables.variablesCode (support p.1 p.2.1 p.2.2.1))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariables
