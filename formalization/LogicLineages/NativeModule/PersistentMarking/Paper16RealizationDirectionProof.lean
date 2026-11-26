module

public import LogicLineages.NativeModule.PersistentMarking.Paper16RealizationDirectionTargets
import LogicLineages.NativeModule.PersistentMarking.NativeClosedBetaChecks
import LogicLineages.NativeModule.PersistentMarking.NativeClosedProof
import LogicLineages.NativeModule.PersistentMarking.NativeClosedStrictWellFoundedChecks
import Mathlib.Tactic.DeriveCountable

namespace LogicLineages.PersistentMarking.Paper16RealizationDirectionProof
open Spine NativeCarrierTargets NativeClosedApplication NativeIndexedCarrierTargets
open NativeIteratorStrictTargets NativeOrdinalRealizationTargets OrdinalRealizationTargets
open Paper16RealizationDirectionTargets

deriving instance Countable for Ty
deriving instance Countable for Head
deriving instance Countable for Expr, Args

private theorem countableRank {X : Type} [Countable X] {r : X → X → Prop}
    (wf : WellFounded r) (a : X) : Countable {β : Ordinal.{0} // β < (wf.apply a).rank} := by
  apply Set.countable_coe_iff.mpr
  apply (Set.countable_range (fun x : X => (wf.apply x).rank)).mono
  intro β hβ
  have below : β < (wf.apply a).rank := hβ
  obtain ⟨b, _, rankAt⟩ := (wf.apply a).mem_range_rank_of_le below.le
  exact ⟨b, rankAt⟩

private theorem baseEdge (S : Signature) :
    ∃ s t : ClosedNativeTerm S indexType, NativeBelow t s := by
  let a : ClosedNativeTerm S indexType :=
    ⟨.lam .ground NativeReduction.zero,
      NativeClosedProof.lambda S .ground .ground _ (NativeClosedProof.zeroNative S)⟩
  have hl : ClosedNative S (.lam indexType a.val) (.arrow indexType indexType) :=
    NativeClosedProof.lambda S indexType indexType _ a.property
  obtain ⟨t, _, _, edge⟩ := NativeClosedBetaChecks.exact_ClosedNativeBeta
    S indexType indexType a.val hl a
  exact ⟨applyClosed ⟨.lam indexType a.val, hl⟩ a, t, edge⟩

public section

/-- In the printed direction a strict base edge would preserve realization at
the rank of its source. The rank of the beta reduct is strictly smaller. -/
theorem exact_PrintedDirectionCounterexample : PrintedDirectionCounterexample := by
  let S : Signature := ⟨[], by simp⟩
  let wf := NativeClosedStrictWellFoundedChecks.exact_ClosedNativeStrictWellFounded S indexType
  obtain ⟨s, t, edge⟩ := baseEdge S
  have countableCarrier : Countable (ClosedNativeTerm S indexType) := inferInstanceAs
    (Countable {q : Expr // ClosedNative S q indexType})
  letI := countableCarrier
  let v : CountableOrdinal := ⟨(wf.apply s).rank, countableRank wf s⟩
  refine ⟨S, wf, s, t, v, edge, le_rfl, ?_⟩
  intro h
  have lower : (wf.apply t).rank < (wf.apply s).rank := (wf.apply s).rank_lt_of_rel edge
  exact lower.not_ge h

theorem exact_NotPrintedRealization : ¬ PrintedRealization := by
  intro h
  obtain ⟨S, _, s, t, v, edge, hs, ht⟩ := exact_PrintedDirectionCounterexample
  obtain ⟨_, forward, _, _⟩ := h.1.2.2 S
  exact ht (forward .base s t v edge hs)

#print axioms exact_PrintedDirectionCounterexample
#print axioms exact_NotPrintedRealization

end LogicLineages.PersistentMarking.Paper16RealizationDirectionProof
