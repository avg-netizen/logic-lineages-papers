module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLiveRootSuccessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenScratchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralChosenRootSuccessProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawTick
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickOpenScratchProof (liveRead)
open NumberedWindowInternalLiteralLiveRootSuccessProof (D exact_OpenLiveRootSuccess)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Invert the actual scratch transition at any physical nonempty
frame. A new nonzero flag yields the successful root callback on
that frame's own source, witness, and destination, irrespective of
the previous flag or the destination scratch frame. -/
theorem exact_OpenChosenRootSuccess (p other : Program 3)
    (flag q w r k f : OTerm α)
    (held : D B Γ (programGraph (chosenTick p other) (stateTerm (suc k) f)
      ![stateTerm flag (frameValueTerm q w r)])) :
    D B Γ (programGraph (rootCall p) (suc k) ![q,w,r]) := by
  let start := stateTerm flag (frameValueTerm q w r)
  let stop := stateTerm (suc k) f
  let tape : Fin 3 → OTerm α := ![q,w,r]
  let input : Fin 1 → OTerm α := ![start]
  obtain ⟨frame,hq,hw,hr⟩ := liveRead (body := B) (Γ := Γ) flag q w r
  have literal := successorBranchElim stateFrame (.projection 0) (performLive p other)
    stop (packedBody [q,w,r]) input frame held
  have tick : D B Γ (programGraph (liveTick p other) stop tape) := by
    apply compositionRecover (liveTick p other) ![rowSource,rowWitness,rowDestination]
      stop input tape literal
    intro i
    exact Fin.cases hq (Fin.cases hw (Fin.cases hr (fun e => Fin.elim0 e))) i
  exact exact_OpenLiveRootSuccess p other k f tape tick

#print axioms exact_OpenChosenRootSuccess
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralChosenRootSuccessProof
