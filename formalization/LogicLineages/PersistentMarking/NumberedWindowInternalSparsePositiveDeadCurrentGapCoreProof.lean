module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveChosenConsSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputFinishProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationTerminalChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationSuccessorProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationHeadChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentGapCoreProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseFieldInductionTargets (malformed)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)
open NumberedWindowInternalSparsePositiveFoldOpenChecks (exact_OpenMalformedCollapse)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (moveFuel)
open NumberedWindowInternalSparsePositiveIterationTerminalChecks (exact_OpenTerminalNilLoop)
open NumberedWindowInternalSparsePositiveIterationHeadChecks (exact_OpenHeadFirstShift)
open NumberedWindowInternalSparsePositiveOutputFinishProof (terminalValue)
open NumberedWindowInternalSparsePositiveChosenConsSyntaxProof (finishGraph)

theorem deadAtSeeds {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3) (ctx ty current cert pred old dead : OTerm α)
    (equal : Nonempty (Derivation body Γ (eqn cert (suc pred))))
    (gap : Nonempty (Derivation body Γ (malformed cert)))
    (before : Nonempty (Derivation body Γ (scratchGraph old cert current)))
    (after : Nonempty (Derivation body Γ (scratchGraph dead z z))) :
    Nonempty (Derivation body Γ (finishGraph raw least z ctx ty current cert)) := by
  obtain ⟨b⟩ := before
  obtain ⟨a⟩ := after
  obtain ⟨g⟩ := gap
  have badStep := exact_OpenMalformedCollapse body raw least α dead z old ctx ty current cert cert current
  obtain ⟨step⟩ := closedApply badStep
    ⟨Derivation.conjunctionIntroduction b (Derivation.conjunctionIntroduction g a)⟩
  have moved := exact_OpenHeadFirstShift body raw least α dead pred ctx ty current cert z z old dead
  obtain ⟨shift⟩ := closedApply moved
    ⟨Derivation.conjunctionIntroduction b (Derivation.conjunctionIntroduction a step)⟩
  obtain ⟨stable⟩ := closedApply (exact_OpenTerminalNilLoop body raw least α dead pred ctx ty z) ⟨a⟩
  have original := Derivation.implicationElimination (Derivation.conjunctionRight shift) stable
  obtain ⟨e⟩ := equal
  have chosen := moveFuel raw least dead (suc pred) cert ctx ty current cert ⟨symm e⟩ ⟨original⟩
  exact terminalValue raw least dead ctx ty current cert z z chosen ⟨a⟩ ⟨refl z⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentGapCoreProof
