module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalArithmeticPrograms LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- Standard evaluation calibration, never a reflection rule. -/
def ExactAdditionEvaluation : Prop :=
  ∀ x y : Nat, evaluate addition (x ::ᵥ y ::ᵥ List.Vector.nil) = x+y

def ExactMultiplicationEvaluation : Prop :=
  ∀ x y : Nat, evaluate multiplication (x ::ᵥ y ::ᵥ List.Vector.nil) = x*y

/-- Exact original-calculus graph law for all free-variable types and terms. -/
def ActualOriginalAdditionGraph : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (out x y : OrdinaryArithmetic.Term α),
  let g := programGraph addition out (Fin.cons x (Fin.cons y Fin.elim0))
  let s := equal out (OrdinaryArithmetic.addTerm x y)
  Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

def ActualOriginalMultiplicationGraph : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (out x y : OrdinaryArithmetic.Term α),
  let g := programGraph multiplication out (Fin.cons x (Fin.cons y Fin.elim0))
  let s := equal out (OrdinaryArithmetic.mulTerm x y)
  Nonempty (Derivation body [] ((g.imp s) ⊓ (s.imp g)))

def ActualOriginalAdditionTotalFunctional : Prop :=
  ∀ body : Positive (Fin 1),
  Total body (OrdinaryArithmetic.graphFormula addition) ∧
    Functional body (OrdinaryArithmetic.graphFormula addition)

def ActualOriginalMultiplicationTotalFunctional : Prop :=
  ∀ body : Positive (Fin 1),
  Total body (OrdinaryArithmetic.graphFormula multiplication) ∧
    Functional body (OrdinaryArithmetic.graphFormula multiplication)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsTargets
