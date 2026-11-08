module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalListCodec InternalRawListRepeat
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Nil returns the original symbolic initial state. -/
def ActualOriginalRawListRepeatZero : Prop :=
  ∀ (body : Positive (Fin 1)) (transition : Program 1) (α : Type)
    (out initial : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((repeatGraph transition out OrdinaryArithmetic.zeroTerm initial).iff
      (equal out initial)))

/-- The ordinary foldr cons law, retaining the actual original constructor
and the actual graph of the supplied tail result. -/
def ActualOriginalRawListRepeatCons : Prop :=
  ∀ (body : Positive (Fin 1)) (transition : Program 1) (α : Type)
    (code head tail tailResult out initial : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    (((programGraph consCode code (Fin.cons head (Fin.cons tail Fin.elim0))) ⊓
      (repeatGraph transition tailResult tail initial)).imp
      ((repeatGraph transition out code initial).iff
        (programGraph transition out (Fin.cons tailResult Fin.elim0)))))

/-- One original constructor cell may instead apply the transition to the
initial state first. All codes, states and outputs remain arbitrary symbolic
arithmetic terms, and every transition is an actual unary original PR AST. -/
def ActualOriginalRawListRepeatFrontCons : Prop :=
  ∀ (body : Positive (Fin 1)) (transition : Program 1) (α : Type)
    (code head tail out initial next : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    (((programGraph consCode code (Fin.cons head (Fin.cons tail Fin.elim0))) ⊓
      (programGraph transition next (Fin.cons initial Fin.elim0))).imp
      ((repeatGraph transition out code initial).iff
        (repeatGraph transition out tail next))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatTargets
