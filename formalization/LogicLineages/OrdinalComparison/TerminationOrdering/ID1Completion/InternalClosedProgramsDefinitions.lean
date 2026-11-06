module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionFreeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedPrograms
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

abbrev allBlock {α : Type} {k : Nat} (phi : Formula (α ⊕ Fin k)) : Formula α :=
  (BoundedFormula.relabel (id : α ⊕ Fin k → α ⊕ Fin k) phi).alls

/-- One CLOSED ordinary first-order sentence: every input tuple has an output
satisfying the unchanged original compiler graph. -/
def totalSentence {n : Nat} (p : Program n) : OFormula Empty :=
  OrdinaryArithmetic.forallFin (OrdinaryArithmetic.existsFin
    (OrdinaryArithmetic.applyGraph (OrdinaryArithmetic.graphFormula p)
      (.var (Sum.inr (0 : Fin 1) : (Empty ⊕ Fin n) ⊕ Fin 1))
      (fun i => .var (.inl (.inr i)))))

/-- One CLOSED ordinary first-order sentence: any two graph outputs agree.
Output indices are 0 and 1; the n inputs follow in original Fin order. -/
def uniqueSentence {n : Nat} (p : Program n) : OFormula Empty :=
  OrdinaryArithmetic.forallFin
    ((OrdinaryArithmetic.applyGraph (OrdinaryArithmetic.graphFormula p)
        (.var (Sum.inr (0 : Fin (n+2)) : Empty ⊕ Fin (n+2)))
        (fun i => .var (.inr i.succ.succ)) ⊓
      OrdinaryArithmetic.applyGraph (OrdinaryArithmetic.graphFormula p)
        (.var (.inr 1)) (fun i => .var (.inr i.succ.succ))).imp
      ((Term.var (Sum.inr (0 : Fin (n+2)) : Empty ⊕ Fin (n+2))).equal (.var (.inr 1))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedPrograms
