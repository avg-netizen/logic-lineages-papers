module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeLiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenScratchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeTickProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (programRename outputTransport projectionValue valueUnique zeroSuccessorCases)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalQuotientComparisonProof (orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseRawTick
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickOpenScratchProof (frameRead)
open NumberedWindowInternalSparseRawTickShapeTargets
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (goodRename goodIntro stateRename)
open NumberedWindowInternalSparseRawTickShapeLiveProof (liveShape)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- One actual tick at an arbitrary pack-shaped scratch. The physical
frame read is split by the arithmetic zero/successor rule. A zero frame
selects the literal projection, whose supplied output is the same input
scratch; a successor frame selects `performLive`, whose row selectors
are eliminated as object eigenvariables and never interpreted. -/
theorem tickShape (p other : Program 3) (flag frame out : OTerm α)
    (h : Nonempty (Derivation body Γ
      (programGraph (chosenTick p other) out ![stateTerm flag frame]))) :
    Nonempty (Derivation body Γ (goodState out)) := by
  let st := stateTerm flag frame
  apply zeroSuccessorCases Γ frame (goodState out)
  · obtain ⟨dr⟩ := frameRead (body := body) (Γ := Γ) flag frame
    obtain ⟨dh⟩ := h
    have hz : Nonempty (Derivation body (eqn frame z :: Γ) (programGraph stateFrame z ![st])) :=
      outputTransport stateFrame frame z ![st]
        ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp dr _⟩
    have hp := zeroBranchElim stateFrame (.projection 0) (performLive p other) out ![st] hz
      ⟨addHyp dh _⟩
    have hv : Nonempty (Derivation body (eqn frame z :: Γ)
        (programGraph (.projection 0) st ![st])) := projectionValue 0 ![st]
    have he := valueUnique (.projection 0) out st ![st] hp hv
    exact goodIntro out flag frame he ⟨orRight (Derivation.hypothesis List.mem_cons_self)⟩
  · intro β j Δ v hj he
    rw [goodRename]
    let st' := stateTerm (flag.relabel j) (frame.relabel j)
    have h' := renameInto h j Δ hj
    rw [programRename,inputsRename,stateRename] at h'
    have read : Nonempty (Derivation body Δ (programGraph stateFrame (frame.relabel j) ![st'])) :=
      frameRead (flag.relabel j) (frame.relabel j)
    have hs := outputTransport stateFrame (frame.relabel j) (suc v) ![st'] he read
    have hl := successorBranchElim stateFrame (.projection 0) (performLive p other)
      (out.relabel j) v ![st'] hs h'
    apply programCompositionCases (liveTick p other) ![rowSource,rowWitness,rowDestination]
      (out.relabel j) ![st'] (goodState (out.relabel j)) hl
    intro γ k ys Θ _ hlive _
    rw [goodRename]
    exact liveShape p other _ ys hlive

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeTickProof
