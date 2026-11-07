module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalSquareRoot InternalSquareRootArithmetic
/-- The target is an actual original-calculus derivation for arbitrary
free-variable types and terms, not an assertion restricted to numerals. -/
def ActualOriginalSquareRootGraph : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (out n : OrdinaryArithmetic.Term α),
  let g := programGraph root out (Fin.cons n Fin.elim0)
  let s := interval out n
  Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))
def ActualOriginalSquareRootTotalFunctional : Prop :=
  ∀ body : Positive (Fin 1),
  InternalGraphComposition.Total body (OrdinaryArithmetic.graphFormula root) ∧
    InternalGraphComposition.Functional body (OrdinaryArithmetic.graphFormula root)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootTargets
