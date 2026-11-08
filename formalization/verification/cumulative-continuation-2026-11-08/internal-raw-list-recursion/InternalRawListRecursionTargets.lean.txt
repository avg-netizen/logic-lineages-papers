module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalRawListRecursion InternalListCodec NumberedMultisetNumeric
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All-input calibration to recursion on the unchanged decoded list. -/
def ActualRawListRecursionEvaluation : Prop :=
  ∀ (k : Nat) (base : Program k) (step : Program (k + 2))
    (params : List.Vector Nat k) (code : Nat),
  evaluate (listRec base step) (code ::ᵥ params) =
    ((decodeNumbers code).getD []).foldr
      (fun head result => evaluate step (head ::ᵥ result ::ᵥ params)) (evaluate base params)

/-- Actual graph equivalence at the original nil code, with arbitrary
symbolic parameters and output. -/
def ActualOriginalListRecursionZero : Prop :=
  ∀ (body : Positive (Fin 1)) (k : Nat) (base : Program k) (step : Program (k + 2))
    (α : Type) (out : OrdinaryArithmetic.Term α) (params : Fin k → OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((recGraph base step out OrdinaryArithmetic.zeroTerm params).iff
      (programGraph base out params)))

/-- Actual unfolding on the literal original cons graph. Every raw head and
tail code is covered; the recursive call retains every original parameter. -/
def ActualOriginalListRecursionCons : Prop :=
  ∀ (body : Positive (Fin 1)) (k : Nat) (base : Program k) (step : Program (k + 2))
    (α : Type) (code head tail out : OrdinaryArithmetic.Term α)
    (params : Fin k → OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((programGraph consCode code (Fin.cons head (Fin.cons tail Fin.elim0))).imp
      ((recGraph base step out code params).iff (consStep base step out head tail params))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionTargets
