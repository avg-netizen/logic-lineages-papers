module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonNilProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGateProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonCoreProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc hopCodeTerm hopCertified)
open NumberedWindowInternalSparsePathEnvelopeOpenChecks (exact_OpenHopEnvelope)
open NumberedWindowInternalSparsePathAdvanceTargets (actualCalls)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGateProof (acceptCalls)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (headData positiveAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof (provideHead)
open NumberedWindowInternalSparsePositiveHeadDecompositionChecks (exact_OpenPositiveHeadDecomposition)
open NumberedWindowInternalSparseAddressSingletonTargets
open NumberedWindowInternalSparseAddressSingletonNilProof (finishNil)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem literalHop (dst q w r : OTerm α) :
    Nonempty (Derivation body Γ (hopCertified (hopCodeTerm dst q w r) dst q w r)) := by
  let hop := hopCodeTerm dst q w r
  obtain ⟨eqv⟩ := exact_OpenHopEnvelope body α hop dst q w r
  have fixed : Nonempty (Derivation body Γ (equal hop (hopCodeTerm dst q w r))) := by
    rw [equalEqn]
    exact ⟨refl hop⟩
  exact closedApply ⟨Derivation.conjunctionLeft eqv⟩ fixed

theorem fromCalls (raw : Program 5) (least : Program 3) (ctx ty src dst q w r : OTerm α)
    (known : Nonempty (Derivation body Γ (actualCalls raw least ctx ty src dst q w r))) :
    Nonempty (Derivation body Γ (positiveAt raw least ctx ty src (singletonCertificate dst q w r) dst)) := by
  let head := hopCodeTerm dst q w r
  let cert := singletonCertificate dst q w r
  obtain ⟨calls⟩ := known
  obtain ⟨hop⟩ := literalHop (body := body) (Γ := Γ) dst q w r
  obtain ⟨next⟩ := acceptCalls raw least ctx ty src head dst q w r
    ⟨Derivation.conjunctionIntroduction hop calls⟩
  have outer : Nonempty (Derivation body Γ (consGraph cert head z)) :=
    NumberedWindowInternalSparsePairGraphProof.consGraph head z
  obtain ⟨outer⟩ := outer
  obtain ⟨endOf⟩ := finishNil (body := body) (Γ := Γ) raw least ctx ty dst
  have row : Nonempty (Derivation body Γ (headData raw least ctx ty src cert dst head z dst)) :=
    ⟨Derivation.conjunctionIntroduction outer (Derivation.conjunctionIntroduction next endOf)⟩
  have block := provideHead raw least ctx ty src cert dst head z dst row
  obtain ⟨eqv⟩ := exact_OpenPositiveHeadDecomposition body raw least α ctx ty src cert dst
  exact closedApply ⟨Derivation.conjunctionRight eqv⟩ block

theorem core : ExactOpenSingletonCore := by
  intro body raw least α ctx ty src dst q w r
  obtain ⟨d⟩ := fromCalls (body := body) (Γ := [actualCalls raw least ctx ty src dst q w r])
    raw least ctx ty src dst q w r ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonCoreProof
