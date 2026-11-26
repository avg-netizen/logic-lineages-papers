module

public import LogicLineages.NativeModule.PersistentMarking.CutOwnerTargets
public import LogicLineages.NativeModule.PersistentMarking.CutEdgeTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.CutSelectionTargets
open Spine ExtendedMeasure

/-- Actual Select/PSelect right-root cut step. Only the concrete continuation
is supplied to the bounded primary IH; the intermediate may be marked. -/
def Selection : Prop := ∀ S n, CutEdgeTargets.Below S n →
  ∀ f sb se g tb te τ q i domains args r u,
  CutOwnerSyntax.Root S f sb se g tb te →
  PaperTerm S (.marked f τ sb se) τ → PaperTerm S (.marked g τ tb te) τ →
  PaperTerm S u τ → (At tb i q ∨ At te i q) →
  Typed EmptyContext q (ArrowPrefix domains τ) → PrefixTuple g tb te domains args →
  apply q args = some r → ∀ continuation : ExtendedWeakTree S r u,
  treeSize continuation < n → Ordinary u → ExtendedWeak S (.marked f τ sb se) u
end LogicLineages.PersistentMarking.CutSelectionTargets
