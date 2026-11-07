module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureTotalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureFunctionalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionFreeInitialProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureProof
open InternalRecursionFreeInitialProof InternalRecursionClosureTotalityProof InternalRecursionClosureFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Structural induction on the original arity-indexed Program syntax.
The recursion branch is now paid by internal PA induction, not excluded. -/
theorem actualOriginalPrograms : InternalRecursionClosureTargets.ActualOriginalPrograms := by
  intro body n p
  induction p with
  | zero =>
    exact ⟨(actualInitialGraphTotality body).1,(actualInitialGraphFunctionality body).1⟩
  | succ =>
    exact ⟨(actualInitialGraphTotality body).2.1,(actualInitialGraphFunctionality body).2.1⟩
  | projection i =>
    exact ⟨(actualInitialGraphTotality body).2.2 _ i,(actualInitialGraphFunctionality body).2.2 _ i⟩
  | composition f g ihf ihg =>
    exact InternalGraphCompositionProof.actualOriginalProgramComposition body _ _ f g
      ihf.1 (fun i => (ihg i).1) ihf.2 (fun i => (ihg i).2)
  | recursion f g ihf ihg =>
    exact ⟨actualOriginalRecursionTotality body _ (OrdinaryArithmetic.graphFormula f)
      (OrdinaryArithmetic.graphFormula g) ihf.1 ihg.1,
      actualOriginalRecursionFunctionality body _ (OrdinaryArithmetic.graphFormula f)
        (OrdinaryArithmetic.graphFormula g) ihf.2 ihg.2⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureProof
