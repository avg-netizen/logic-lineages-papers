module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionFreeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalClosedPrograms
open InternalClosedProgramsBindingProof InternalFiniteBlocksBindingProof InternalRecursionFreeProof

theorem actualClosedOriginalProgramSentences : InternalClosedProgramsTargets.ActualClosedOriginalProgramSentences := by
  intro body n p hp
  obtain ⟨ht,hu⟩ := actualOriginalRecursionFreePrograms body n p hp
  constructor
  · unfold totalSentence
    rw [actualOriginalUniversalEmbedding]
    apply actualFiniteUniversalIntroduction body Empty n []
    rw [actualOriginalBlockEmbedding]
    exact ht (Empty ⊕ Fin n) (fun i => .var (.inr i))
  · unfold uniqueSentence
    rw [actualOriginalUniversalEmbedding]
    apply actualFiniteUniversalIntroduction body Empty (n+2) []
    exact hu (Empty ⊕ Fin (n+2)) (.var (.inr 0)) (.var (.inr 1))
      (fun i => .var (.inr i.succ.succ))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsProof
