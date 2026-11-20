module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityFuelProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityShiftProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityNilProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldExistentialProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityGapProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseFieldInductionTargets (malformed nonzero)
open NumberedWindowInternalSparseFieldExistentialProof (someConsRename)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph loopGraph)
open NumberedWindowInternalSparsePositiveFoldOpenChecks (exact_OpenMalformedCollapse)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (moveLoop moveFuel)
open NumberedWindowInternalSparsePositiveIterationBindingProof (scratchRename)
open NumberedWindowInternalSparsePositiveTerminalityTargets (terminalScratch)
open NumberedWindowInternalSparsePositiveTerminalityScratchBindingProof (terminalRename)
open NumberedWindowInternalSparsePositiveTerminalityFuelProof (fuelSuccessorCases)
open NumberedWindowInternalSparsePositiveTerminalitySeedProof (scratchCases)
open NumberedWindowInternalSparsePositiveTerminalityShiftProof (shift)
open NumberedWindowInternalSparsePositiveTerminalityNilProof (fromNil)

private theorem notRename {α β : Type} (p : Formula α) (j : α → β) :
    (p.not).relabel j = (p.relabel j).not := rfl

theorem gapRename {α β : Type} (cert : OTerm α) (j : α → β) :
    (malformed cert).relabel j = malformed (cert.relabel j) := by
  simp only [malformed,nonzero,equalEqn,conjunctionRename,notRename,eqnRelabel,zRelabel,someConsRename]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem afterGap (raw : Program 5) (least : Program 3)
    (out pred ctx ty current cert prior next : OTerm α)
    (loop : Nonempty (Derivation body Γ (loopGraph raw least out (suc pred) ctx ty current cert)))
    (bad : Nonempty (Derivation body Γ (malformed cert)))
    (before : Nonempty (Derivation body Γ (scratchGraph prior cert current)))
    (dead : Nonempty (Derivation body Γ (scratchGraph next z z))) :
    Nonempty (Derivation body Γ (terminalScratch out)) := by
  obtain ⟨p⟩ := before
  obtain ⟨b⟩ := bad
  obtain ⟨d⟩ := dead
  let atStep := exact_OpenMalformedCollapse body raw least α next z prior ctx ty current cert cert current
  have step := closedApply atStep ⟨Derivation.conjunctionIntroduction p (Derivation.conjunctionIntroduction b d)⟩
  exact fromNil raw least out pred ctx ty z (shift raw least out pred ctx ty current cert z z prior next
    ⟨p⟩ ⟨d⟩ step loop)

private theorem pickDead (raw : Program 5) (least : Program 3)
    (out pred ctx ty current cert prior : OTerm α)
    (loop : Nonempty (Derivation body Γ (loopGraph raw least out (suc pred) ctx ty current cert)))
    (bad : Nonempty (Derivation body Γ (malformed cert)))
    (before : Nonempty (Derivation body Γ (scratchGraph prior cert current))) :
    Nonempty (Derivation body Γ (terminalScratch out)) := by
  apply scratchCases z z (terminalScratch out)
  intro β j Δ next hJ dead
  rw [terminalRename]
  rw [zRelabel] at dead
  have d := moveLoop j Δ hJ raw least out (suc pred) ctx ty current cert loop
  rw [sucRelabel] at d
  have b := renameInto bad j Δ hJ
  rw [gapRename] at b
  have p := renameInto before j Δ hJ
  rw [scratchRename] at p
  exact afterGap raw least (out.relabel j) (pred.relabel j) (ctx.relabel j) (ty.relabel j)
    (current.relabel j) (cert.relabel j) (prior.relabel j) next d b p dead

private theorem pickBoth (raw : Program 5) (least : Program 3) (out pred ctx ty current cert : OTerm α)
    (loop : Nonempty (Derivation body Γ (loopGraph raw least out (suc pred) ctx ty current cert)))
    (bad : Nonempty (Derivation body Γ (malformed cert))) :
    Nonempty (Derivation body Γ (terminalScratch out)) := by
  apply scratchCases cert current (terminalScratch out)
  intro β j Δ prior hJ before
  rw [terminalRename]
  have d := moveLoop j Δ hJ raw least out (suc pred) ctx ty current cert loop
  rw [sucRelabel] at d
  have b := renameInto bad j Δ hJ
  rw [gapRename] at b
  exact pickDead raw least (out.relabel j) (pred.relabel j) (ctx.relabel j) (ty.relabel j)
    (current.relabel j) (cert.relabel j) prior d b before

theorem fromGap (raw : Program 5) (least : Program 3) (out fuel ctx ty current cert : OTerm α)
    (bound : Nonempty (Derivation body Γ (ltF cert (suc fuel))))
    (loop : Nonempty (Derivation body Γ (loopGraph raw least out fuel ctx ty current cert)))
    (bad : Nonempty (Derivation body Γ (malformed cert))) :
    Nonempty (Derivation body Γ (terminalScratch out)) := by
  obtain ⟨bad⟩ := bad
  have nz : Nonempty (Derivation body Γ (eqn cert z).not) := by
    rw [← equalEqn]
    exact ⟨Derivation.conjunctionLeft bad⟩
  apply fuelSuccessorCases cert fuel (terminalScratch out) bound nz
  intro β j Δ pred hJ eq _
  rw [terminalRename]
  have b := renameInto ⟨bad⟩ j Δ hJ
  rw [gapRename] at b
  have d := moveLoop j Δ hJ raw least out fuel ctx ty current cert loop
  have d' := moveFuel raw least (out.relabel j) (fuel.relabel j) (suc pred) (ctx.relabel j) (ty.relabel j)
    (current.relabel j) (cert.relabel j) eq d
  exact pickBoth raw least (out.relabel j) pred (ctx.relabel j) (ty.relabel j)
    (current.relabel j) (cert.relabel j) d' b

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityGapProof
