module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenLiveProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue)
open NumberedWindowInternalSparsePathEnvelopeTargets (z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm frameValueTerm)
open NumberedWindowInternalSparseRawTick
open NumberedWindowInternalSparseRawTickTargets
open NumberedWindowInternalSparseRawTickOpenScratchProof (frameRead liveRead)
open NumberedWindowInternalSparseRawTickOpenLiveProof (literalLive)

theorem exact_OpenTerminalTick : ExactOpenTerminalTick := by
  intro body p other α flag
  let st := stateTerm flag z
  let xs : Fin 1 → OTerm α := ![st]
  have hz : Nonempty (Derivation body [] (unary stateFrame z st)) :=
    frameRead (body := body) (Γ := []) flag z
  exact zeroBranchIntro stateFrame (.projection 0) (performLive p other) st xs hz
    (projectionValue 0 xs)

theorem exact_OpenLiftedTick : ExactOpenLiftedTick := by
  intro body p other α flag dom cod arg source child dest
  let src := auxiliaryTerm dom cod source arg
  let wr := functionWitnessTerm child
  let dst := auxiliaryTerm dom cod dest arg
  let initial := stateTerm flag (frameValueTerm src wr dst)
  let final := stateTerm z (frameValueTerm source child dest)
  let xs : Fin 1 → OTerm α := ![initial]
  obtain ⟨found,hq,hw,hr⟩ := liveRead (body := body) (Γ := []) flag src wr dst
  have live := literalLive body p other α dom cod arg source child dest
  have h : Nonempty (Derivation body [] (unary (performLive p other) final initial)) := by
    unfold unary performLive
    apply compositionValue (liveTick p other) ![rowSource,rowWitness,rowDestination] final xs
      ![src,wr,dst] live
    intro i
    exact Fin.cases hq (Fin.cases hw (Fin.cases hr (fun e => Fin.elim0 e))) i
  exact successorBranchIntro stateFrame (.projection 0) (performLive p other) final
    (packedBody [src,wr,dst]) xs found h

#print axioms exact_OpenTerminalTick
#print axioms exact_OpenLiftedTick
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenChecks
