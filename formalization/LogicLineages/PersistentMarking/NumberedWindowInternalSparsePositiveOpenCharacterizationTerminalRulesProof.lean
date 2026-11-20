module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationScratchTransportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputAcceptanceChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationTerminalRulesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFoldTargets (loopGraph scratchGraph)
open NumberedWindowInternalSparsePositiveOutputAcceptanceChecks (exact_OpenPositiveAtTerminal)
open NumberedWindowInternalSparsePositiveOpenCharacterizationBindingProof
open NumberedWindowInternalSparsePositiveOpenCharacterizationScratchTransportProof (moveCurrent)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem recoverAtState (raw : Program 5) (least : Program 3)
    (ctx ty source cert target state current : OTerm α)
    (ok : Nonempty (Derivation body Γ (acceptance raw least ctx ty source cert target)))
    (loop : Nonempty (Derivation body Γ (loopGraph raw least state cert ctx ty (suc source) cert)))
    (pair : Nonempty (Derivation body Γ (scratchGraph state z current))) :
    Nonempty (Derivation body Γ (certificateResult raw least ctx ty source cert target)) := by
  obtain ⟨l⟩ := loop
  obtain ⟨s⟩ := pair
  obtain ⟨rule⟩ := closedApply (exact_OpenPositiveAtTerminal body raw least α
    state ctx ty source cert target current) ⟨Derivation.conjunctionIntroduction l s⟩
  obtain ⟨a⟩ := ok
  have both := Derivation.implicationElimination (Derivation.conjunctionLeft rule) a
  simp only [equalEqn] at both
  have precise := moveCurrent state current (suc target) ⟨Derivation.conjunctionRight both⟩ ⟨s⟩
  obtain ⟨done⟩ := provideState raw least ctx ty source cert target state ⟨l⟩ precise
  exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft both) done⟩

theorem acceptAtState (raw : Program 5) (least : Program 3)
    (ctx ty source cert target state : OTerm α)
    (nonzero : Nonempty (Derivation body Γ (eqn cert z).not))
    (loop : Nonempty (Derivation body Γ (loopGraph raw least state cert ctx ty (suc source) cert)))
    (pair : Nonempty (Derivation body Γ (scratchGraph state z (suc target)))) :
    Nonempty (Derivation body Γ (acceptance raw least ctx ty source cert target)) := by
  obtain ⟨l⟩ := loop
  obtain ⟨s⟩ := pair
  obtain ⟨rule⟩ := closedApply (exact_OpenPositiveAtTerminal body raw least α
    state ctx ty source cert target (suc target)) ⟨Derivation.conjunctionIntroduction l s⟩
  simp only [equalEqn] at rule
  obtain ⟨nz⟩ := nonzero
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight rule)
    (Derivation.conjunctionIntroduction nz (refl (suc target)))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationTerminalRulesProof
