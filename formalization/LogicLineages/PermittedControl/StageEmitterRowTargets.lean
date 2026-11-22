module
public import LogicLineages.PermittedControl.StageCallbackRawLevelTargets
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.StageEmitter
open PreparedProjection (PreparedPacketCode)
open StageCallbackRawLevel (Rendering EntryCode levelCode signedCode rowCode)
open ActualRawComparisonCeiling (LabelCode)
open ActualRawSignedStaticCeiling (RawSyntax)
open ActualBitFamilyRawLayout (RawBitRow)

/-- Effectivity of the four rendering programs of `R`, each uncurried over
its code arguments in their literal order (the same uncurrying as the
`…Effectivity` statements of the rendering modules). -/
structure RenderingEffective (R : Rendering) : Prop where
  append : Primrec₂ R.append
  guard : Primrec (fun p : Nat × List LabelCode × List Nat => R.guard p.1 p.2.1 p.2.2)
  linear : Primrec (fun p : Nat × RawSyntax × Nat × Bool => R.linear p.1 p.2.1 p.2.2.1 p.2.2.2)
  modular : Primrec (fun p : Nat × Nat × RawSyntax × Bool => R.modular p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- The raw level iteration is primitive recursive in (top, start syntax, level). -/
def ExactLevelCodeEffectivity : Prop :=
  ∀ R : Rendering, RenderingEffective R →
    Primrec (fun p : (Nat × RawSyntax) × Nat => levelCode R p.1.1 p.1.2 p.2)

/-- The raw signed packet list is primitive recursive in all its code arguments. -/
def ExactSignedCodeEffectivity : Prop :=
  ∀ R : Rendering, RenderingEffective R →
    Primrec (fun p : Nat × Nat × Bool × Nat × RawSyntax =>
      signedCode R p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

/-- The raw per-row program is primitive recursive in (width, top, raw row). -/
def ExactRowCodeEffectivity : Prop :=
  ∀ R : Rendering, RenderingEffective R →
    Primrec (fun p : Nat × Nat × RawBitRow => rowCode R p.1 p.2.1 p.2.2)

def FullStageEmitterRow : Prop :=
  ExactLevelCodeEffectivity ∧ ExactSignedCodeEffectivity ∧ ExactRowCodeEffectivity

end LogicLineages.PermittedControl.StageEmitter
