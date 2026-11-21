module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreCallProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreForwardProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseApplicationOutputCore
open NumberedWindowInternalSparseApplicationOutputCoreTargets (outputReport)
open NumberedWindowInternalSparseApplicationOutputCoreEmitterProof (objectTape)
open NumberedWindowInternalSparseApplicationOutputCoreCallProof (selectGraph comparison)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
  (tapeRename threeRename auxiliaryRename reportRename reportUnfold reportInstance)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem recover (least : Program 3) (ctx dom cod fn arg y : OTerm α)
    (accepted : Nonempty (Derivation body Γ (programGraph (outputCore least) (suc z)
      (objectTape ctx dom cod fn arg y)))) :
    Nonempty (Derivation body Γ (outputReport least ctx cod (auxiliaryTerm dom cod fn arg) y)) := by
  apply optionGraphCases least ![ctx,cod,auxiliaryTerm dom cod fn arg]
    (outputReport least ctx cod (auxiliaryTerm dom cod fn arg) y)
  · intro β j Δ hJ hz
    have moved := renameInto accepted j Δ hJ
    rw [programRename,tapeRename,sucRelabel,zRelabel] at moved
    rw [threeRename,auxiliaryRename] at hz
    let c := ctx.relabel j
    let d := dom.relabel j
    let t := cod.relabel j
    let f := fn.relabel j
    let a := arg.relabel j
    let out := y.relabel j
    let xs := objectTape c d t f a out
    have stopped := selectGraph least z c d t f a out hz
    have no := zeroBranchElim (selectedLeast least) (constantZero 6) (compareOutput least)
      (suc z) xs stopped moved
    obtain ⟨bad⟩ := valueUnique (constantZero 6) (suc z) z xs no (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · intro β j Δ k hJ selected
    rw [reportRename,auxiliaryRename]
    rw [threeRename,auxiliaryRename] at selected
    have moved := renameInto accepted j Δ hJ
    rw [programRename,tapeRename,sucRelabel,zRelabel] at moved
    let c := ctx.relabel j
    let d := dom.relabel j
    let t := cod.relabel j
    let f := fn.relabel j
    let a := arg.relabel j
    let out := y.relabel j
    let xs := objectTape c d t f a out
    have control := selectGraph least (suc k) c d t f a out selected
    have yes := successorBranchElim (selectedLeast least) (constantZero 6) (compareOutput least)
      (suc z) k xs control moved
    obtain ⟨eq⟩ := (comparison least k c d t f a out control).mp yes
    obtain ⟨actual⟩ := selected
    rw [reportUnfold]
    apply Nonempty.intro
    apply Derivation.existentialIntroduction (emb k)
    rw [reportInstance]
    exact Derivation.conjunctionIntroduction actual eq

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreForwardProof
