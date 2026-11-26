module
public import LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrixTargets
import LogicLineages.PermittedControl.AffineCollapseGuardRowsProof
import LogicLineages.PermittedControl.AffineCollapseGuardRowsReadProof
import LogicLineages.PermittedControl.FixedHeadCollapseGraphCodeProof
import LogicLineages.PermittedControl.NaturalAffineGateGraphSemanticProof
import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrix
open OrdinalComparison FieldComparison
open ArbitraryHeadSharedWire (Valuation)
open NaturalAffineGateGraph (Expression)
open HeterogeneousSignedMatrixSlice (actualRows)
open MixedSameRankResidue (orderedReads actualSum)
open SignedRowSliceValue (valueAt)

private theorem affineExact (f : Nat → Nat) (θ : Valuation) (e : Expression) (out : Nat) :
    actualRows f θ (affineRows e out) [(0,true)] ↔ (NaturalAffineGateGraph.graph out e).eval θ := by
  change (True ∧ valueAt f θ e.1
    (((-1,out) :: e.2).map (fun t => (t.1,.coordinate t.2))) 0 ∧ (0 : Int) = 0 ∧ True) ↔ _
  rw [AffineCollapseGuardRows.coordinatesSum, NaturalAffineGateGraph.signedGraph out e θ]
  simp only [true_and,and_true,eq_self,List.map_cons,List.sum_cons,neg_one_mul,
    NaturalAffineGateGraph.signedValue]
  let s : Int := (e.2.map (fun t => t.1 * (θ t.2 : Int))).sum
  change e.1 + (-(θ out : Int) + s) = 0 ↔ (θ out : Int) = e.1 + s
  omega

private theorem cannotPass (f : Nat → Nat) (θ : Valuation) :
    ¬ actualRows f θ failedRows [(0,true)] := by
  intro h
  have impossible : valueAt f θ 1 [] 0 := h.2.1
  obtain ⟨ys,ordered,he⟩ := impossible
  cases ys with
  | nil =>
      change (1 : Int) + 0 = 0 at he
      omega
  | cons y ys => exact ordered.elim

private theorem hitPaysHead (f : Nat → Nat) (head x y : Nat)
    (hit : FixedHeadCollapseGraph.read f (head,x) = some y) : LimitHead head := by
  have admitted : FixedHeadCollapseGraph.guard (head,x) = true := by
    change closedProperEntryGuard (head,0,x) = true
    cases h : closedProperEntryGuard (head,0,x)
    · simp [FixedHeadCollapseGraph.read,FixedHeadCollapseGraph.fields,
        closedProperEntryResult,h,Option.join] at hit
    · rfl
  have domain := (FixedHeadCollapseGraph.guardExact.2 (head,x)).mp admitted
  exact ⟨domain.1,domain.2.1⟩

private theorem limitScope (f : Nat → Nat) (θ : Valuation) (head : Nat)
    (e : Expression) (i o : Nat) :
    (limitRows head e i o).length = (limitPassing θ head i).length ∧
      (actualRows f θ (limitRows head e i o) (limitPassing θ head i) ↔
        AffineCollapseGraphComposition.graph f head e i o θ) := by
  classical
  by_cases h : LimitHead head
  · let lam := typedHead head h
    have right : rawNoteEncode lam.1 = head := rawNoteEncodeDecode head
    have hlim : Order.IsSuccLimit lam.1.repr := h.2
    have yes := AffineCollapseGuardRows.exactAffineCollapseGuardRows f lam hlim e i o θ
      (AffineCollapseGuardedLow.originalGuardSnapshot lam i θ)
    have trueLayout : AffineCollapseGuardRows.trueSnapshot
        (AffineCollapseGuardedLow.originalGuardSnapshot lam i θ) :=
      ⟨0,(θ i : Int) - (actualOrdinalNorm lam.1.repr : Int),0,rfl⟩
    simp only [limitRows,limitPassing,dif_pos h]
    refine ⟨rfl,?_⟩
    change actualRows f θ (AffineCollapseGuardRows.guardRows lam e i o)
      (AffineCollapseGuardedLow.originalGuardSnapshot lam i θ) ↔ _
    constructor
    · intro checked
      have graph := (yes.mp ⟨checked,trueLayout⟩).1
      rwa [right] at graph
    · intro graph
      exact (yes.mpr ⟨by rwa [right],rfl⟩).1
  · simp only [limitRows,limitPassing,dif_neg h]
    exact ⟨rfl,⟨fun impossible => (cannotPass f θ impossible).elim,
      fun graph => (h (hitPaysHead f head (θ i) (θ o) graph.2)).elim⟩⟩

theorem exactNormalizedBaseRows : ExactNormalizedBaseRows := by
  intro f θ g
  cases g with
  | affine e out => exact ⟨rfl,affineExact f θ e out⟩
  | limitPair head e i o => exact limitScope f θ head e i o

end LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrix
