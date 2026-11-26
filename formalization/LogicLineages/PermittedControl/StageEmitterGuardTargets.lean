module
public import LogicLineages.PermittedControl.StageEmitterHighTargets
public import LogicLineages.PermittedControl.StageCallbackRenderLinearTargets
public import LogicLineages.PermittedControl.StageCallbackRenderModularTargets

@[expose] public section
namespace LogicLineages.PermittedControl.StageEmitter
open PreparedProjection (PreparedPacketCode)
open StageCallbackRawLevel (Rendering)
open RawPacketAlgebra (encodePacket appendCode)
open ClosedBlockDecision (ClosedBlockDecision)
open MixedSameRankResidue (WeightedOperand)
open ActualRawComparisonCeiling (LabelCode encodeLabel)
open ActualFullValueLabels (labels)
open ActualFullLabelPairGuards (Answer)

/-- The `guard` field of `Rendering.Exact`, copied literally, for one program. -/
def GuardExact (g : Nat → List LabelCode → List Nat → PreparedPacketCode) : Prop :=
  ∀ (top : Nat) (grouped : List WeightedOperand) (a : List Answer),
    g top ((labels grouped).map encodeLabel) (a.map Answer.code) =
      encodePacket (StageCallbackCanonicalRoutes.guard top grouped a)

/-- The `guard` field of `RenderingEffective`, for one program. -/
def GuardEffective (g : Nat → List LabelCode → List Nat → PreparedPacketCode) : Prop :=
  Primrec (fun p : Nat × List LabelCode × List Nat => g p.1 p.2.1 p.2.2)

/-- The rendering with the three gated programs (Opus B's `appendCode`,
Fable-2's `linearCode` and `modularCode`) and a guard program `g`. -/
def renderingWith (g : Nat → List LabelCode → List Nat → PreparedPacketCode) : Rendering :=
  ⟨appendCode,g,StageCallbackRender.linearCode,StageCallbackRender.modularCode⟩

def ExactRenderingFromGuard : Prop :=
  ∀ g, GuardExact g → GuardEffective g → (renderingWith g).Exact ∧ RenderingEffective (renderingWith g)

/-- The comparator of `thm:arithmetic` from one exact, primitive recursive guard program. -/
def ExactClosedBlockDecisionFromGuard : Prop :=
  ∀ g, GuardExact g → GuardEffective g → ClosedBlockDecision

def FullStageEmitterGuard : Prop := ExactRenderingFromGuard ∧ ExactClosedBlockDecisionFromGuard

end LogicLineages.PermittedControl.StageEmitter
