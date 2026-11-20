module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalitySeedProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationHeadChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityShiftProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph loopGraph stepGraph)
open NumberedWindowInternalSparsePositiveIterationHeadChecks (exact_OpenHeadFirstShift)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem shift (raw : Program 5) (least : Program 3)
    (out fuel ctx ty oldCurrent oldCert newCurrent newCert prior next : OTerm α)
    (old : Nonempty (Derivation body Γ (scratchGraph prior oldCert oldCurrent)))
    (new : Nonempty (Derivation body Γ (scratchGraph next newCert newCurrent)))
    (hStep : Nonempty (Derivation body Γ (stepGraph raw least next z prior ctx ty oldCurrent oldCert)))
    (loop : Nonempty (Derivation body Γ (loopGraph raw least out (suc fuel) ctx ty oldCurrent oldCert))) :
    Nonempty (Derivation body Γ (loopGraph raw least out fuel ctx ty newCurrent newCert)) := by
  obtain ⟨a⟩ := old
  obtain ⟨b⟩ := new
  obtain ⟨s⟩ := hStep
  have h := exact_OpenHeadFirstShift body raw least α out fuel ctx ty oldCurrent oldCert
    newCurrent newCert prior next
  obtain ⟨equiv⟩ := closedApply h
    ⟨Derivation.conjunctionIntroduction a (Derivation.conjunctionIntroduction b s)⟩
  obtain ⟨l⟩ := loop
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft equiv) l⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityShiftProof
