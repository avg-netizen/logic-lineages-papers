module
public import LogicLineages.PermittedControl.StageCallbackGuardRenderTargets
public import LogicLineages.PermittedControl.StageCallbackRenderLinearTargets
public import LogicLineages.PermittedControl.StageCallbackRenderModularTargets
public import LogicLineages.PermittedControl.StageEmitterRowTargets

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackGuardRender
open StageCallbackRawLevel (Rendering)

/-- The concrete rendering record, in the field order of `Rendering`. -/
def R₀ : Rendering :=
  ⟨RawPacketAlgebra.appendCode,guardCode,StageCallbackRender.linearCode,StageCallbackRender.modularCode⟩

def ExactR₀ : Prop := Rendering.Exact R₀

/-- Exactly Opus A's hypothesis form `StageEmitter.RenderingEffective`. -/
def EffectiveR₀ : Prop := StageEmitter.RenderingEffective R₀

def FullR₀ : Prop := ExactR₀ ∧ EffectiveR₀

end LogicLineages.PermittedControl.StageCallbackGuardRender
