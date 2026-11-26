module

public import LogicLineages.NativeModule.PersistentMarking.RefinementSyntaxTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.RefinementAppendTargets
open Spine

def OmitSuffix : Prop := ∀ S f τ base extras tail,
  PaperTerm S (.marked f τ base (extras.append tail)) τ →
  PaperTerm S (.marked f τ base extras) τ →
  Refines S (.marked f τ base (extras.append tail)) (.marked f τ base extras)

/-- Both actual appended tuples are supplied positionwise by finite refinement
witnesses. Output annotation may be retyped, as allowed by the source. -/
def MarkedAppend : Prop := ∀ S f σ τ qb qe sb se as bs,
  Refines S (.marked f σ qb qe) (.marked f σ sb se) →
  _root_.Nonempty (RefinementBasesTree S as bs) →
  Refines S (.marked f τ qb (qe.append as)) (.marked f τ sb (se.append bs))

def HeadAppend : Prop := ∀ S f τ qb sb as bs,
  Refines S (.head f qb) (.head f sb) →
  _root_.Nonempty (RefinementBasesTree S as bs) →
  Refines S (.marked f τ qb as) (.marked f τ sb bs)
end LogicLineages.PersistentMarking.RefinementAppendTargets
