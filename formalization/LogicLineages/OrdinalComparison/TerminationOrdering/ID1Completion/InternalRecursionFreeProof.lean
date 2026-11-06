module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionFreeInitialProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionFreeProof
open InternalRecursionFreeInitialProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalRecursionFreePrograms : InternalRecursionFreeTargets.ActualOriginalRecursionFreePrograms := by
  intro body n p
  induction p with
  | zero =>
    intro _
    exact ⟨(actualInitialGraphTotality body).1,(actualInitialGraphFunctionality body).1⟩
  | succ =>
    intro _
    exact ⟨(actualInitialGraphTotality body).2.1,(actualInitialGraphFunctionality body).2.1⟩
  | projection i =>
    intro _
    exact ⟨(actualInitialGraphTotality body).2.2 _ i,(actualInitialGraphFunctionality body).2.2 _ i⟩
  | composition f g ihf ihg =>
    intro hp
    obtain ⟨hf,hg⟩ := hp
    exact InternalGraphCompositionProof.actualOriginalProgramComposition body _ _ f g
      (ihf hf).1 (fun i => (ihg i (hg i)).1) (ihf hf).2 (fun i => (ihg i (hg i)).2)
  | recursion f g _ _ =>
    intro hp
    exact False.elim hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionFreeProof
