module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityShiftProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldExistentialProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityConsShiftProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparseFieldExistentialProof (consGraphRename)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePathAdvanceOpenSyntaxProof (moveQuad)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph loopGraph)
open NumberedWindowInternalSparsePositiveFoldOpenChecks (exact_OpenConsUpdate)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (moveLoop loopRename)
open NumberedWindowInternalSparsePositiveIterationBindingProof (scratchRename)
open NumberedWindowInternalSparsePositiveTerminalitySeedProof (scratchCases)
open NumberedWindowInternalSparsePositiveTerminalityShiftProof (shift)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem shifted (raw : Program 5) (least : Program 3)
    (out pred ctx ty current cert hd tl next prior after : OTerm α)
    (loop : Nonempty (Derivation body Γ (loopGraph raw least out (suc pred) ctx ty current cert)))
    (cell : Nonempty (Derivation body Γ (consGraph cert hd tl)))
    (advanced : Nonempty (Derivation body Γ (selectedGraph raw least next ctx ty current hd)))
    (old : Nonempty (Derivation body Γ (scratchGraph prior cert current)))
    (new : Nonempty (Derivation body Γ (scratchGraph after tl next))) :
    Nonempty (Derivation body Γ (loopGraph raw least out pred ctx ty next tl)) := by
  obtain ⟨cell⟩ := cell
  obtain ⟨advanced⟩ := advanced
  obtain ⟨old⟩ := old
  obtain ⟨new⟩ := new
  let atStep := exact_OpenConsUpdate body raw least α after z prior ctx ty current cert cert current hd tl next
  have tookStep := closedApply atStep
    ⟨Derivation.conjunctionIntroduction old (Derivation.conjunctionIntroduction cell
      (Derivation.conjunctionIntroduction advanced new))⟩
  exact shift raw least out pred ctx ty current cert next tl prior after ⟨old⟩ ⟨new⟩ tookStep loop

private theorem pickUpdated (raw : Program 5) (least : Program 3)
    (out pred ctx ty current cert hd tl next prior : OTerm α)
    (loop : Nonempty (Derivation body Γ (loopGraph raw least out (suc pred) ctx ty current cert)))
    (cell : Nonempty (Derivation body Γ (consGraph cert hd tl)))
    (advanced : Nonempty (Derivation body Γ (selectedGraph raw least next ctx ty current hd)))
    (old : Nonempty (Derivation body Γ (scratchGraph prior cert current))) :
    Nonempty (Derivation body Γ (loopGraph raw least out pred ctx ty next tl)) := by
  apply scratchCases tl next (loopGraph raw least out pred ctx ty next tl)
  intro β j Δ after hJ new
  rw [loopRename]
  have l := moveLoop j Δ hJ raw least out (suc pred) ctx ty current cert loop
  rw [sucRelabel] at l
  have cell' := renameInto cell j Δ hJ
  rw [consGraphRename] at cell'
  have advanced' := moveQuad j Δ hJ (advance raw least) next ctx ty current hd advanced
  have old' := renameInto old j Δ hJ
  rw [scratchRename] at old'
  exact shifted raw least (out.relabel j) (pred.relabel j) (ctx.relabel j) (ty.relabel j)
    (current.relabel j) (cert.relabel j) (hd.relabel j) (tl.relabel j) (next.relabel j) (prior.relabel j)
    after l cell' advanced' old' new

theorem shiftCons (raw : Program 5) (least : Program 3)
    (out pred ctx ty current cert hd tl next : OTerm α)
    (loop : Nonempty (Derivation body Γ (loopGraph raw least out (suc pred) ctx ty current cert)))
    (cell : Nonempty (Derivation body Γ (consGraph cert hd tl)))
    (advanced : Nonempty (Derivation body Γ (selectedGraph raw least next ctx ty current hd))) :
    Nonempty (Derivation body Γ (loopGraph raw least out pred ctx ty next tl)) := by
  apply scratchCases cert current (loopGraph raw least out pred ctx ty next tl)
  intro β j Δ prior hJ old
  rw [loopRename]
  have l := moveLoop j Δ hJ raw least out (suc pred) ctx ty current cert loop
  rw [sucRelabel] at l
  have cell' := renameInto cell j Δ hJ
  rw [consGraphRename] at cell'
  have advanced' := moveQuad j Δ hJ (advance raw least) next ctx ty current hd advanced
  exact pickUpdated raw least (out.relabel j) (pred.relabel j) (ctx.relabel j) (ty.relabel j)
    (current.relabel j) (cert.relabel j) (hd.relabel j) (tl.relabel j) (next.relabel j) prior l cell' advanced' old

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTerminalityConsShiftProof
