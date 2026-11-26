import LogicLineages.PersistentMarking.CutEdgeTargets
namespace LogicLineages.PersistentMarking.CutCoreTargets
open Spine ExtendedMeasure

/-- Secondary induction: the right comparison and intermediate/final endpoints
stay fixed; only an actual strictly smaller left weak tree can be used. -/
def LeftBelow (S : Signature) (t u : Expr) (m : Nat) : Prop :=
  ∀ s (left : ExtendedWeakTree S s t), treeSize left < m →
    Ordinary u → ExtendedWeak S s u

/-- Exact lexicographic step, with all actual witness counts explicit. -/
def Step : Prop := ∀ S n, CutEdgeTargets.Below S n →
  ∀ s t u (left : ExtendedWeakTree S s t) (right : ExtendedWeakTree S t u),
  treeSize right = n → LeftBelow S t u (treeSize left) →
  Ordinary u → ExtendedWeak S s u

/-- First stage of the printed theorem, prior to checked conservative elimination. -/
def AuxiliaryCut : Prop := ∀ S s t u,
  ExtendedWeak S s t → ExtendedWeak S t u → Ordinary u → ExtendedWeak S s u

/-- The original already-frozen source conclusion, unchanged. -/
def FullCut : Prop := AuxiliaryTargets.OrdinaryFinalCut
end LogicLineages.PersistentMarking.CutCoreTargets
