module
public import LogicLineages.PermittedControl.ActualGreatestRouteResidualTargets
import LogicLineages.PermittedControl.PreparedParameterActualProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphSupportProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualGreatestRouteResidual
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open SourceTermGraphSupportProof (formula_eval_congr)
open PreparedProjection
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRoutePacket (Shape)
open ActualSelectedSignedRouteProjection (LowerHolds)
open OriginalMatrixLinearLowerTable (Live assignment)

theorem keepMember (top : Nat) (qs : List Packet) (q : Packet) :
    q ∈ keep top qs ↔ q ∈ qs ∧ StrictLower top q.1 := by
  simp only [keep,List.mem_filter,List.all_eq_true,decide_eq_true_eq,StrictLower]

theorem tiedStrictLive (f ρ : Nat → Nat) (top : Nat) (ops : List LowerOperand) (ν : Nat → Nat)
    (tied : PreparedTableTied f top ρ ops ν) : StrictLower top ops ∧ Live f ρ ops := by
  have realizedSlot (op : LowerOperand) (used : op ∈ ops) :
      op.rank < top ∧ ∃ v : Nat, lowerOperandRead f ρ op = some (some v) := by
    obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp used
    have one := tied j hj
    change ops[j].rank < top ∧ LowerOperandActual f ρ ops[j] (ν (j+1)) at one
    rw [eq] at one
    exact ⟨one.1,ν (j+1),(preparedTiedProjection.1 f ρ op _).mpr one.2⟩
  exact ⟨fun op used => (realizedSlot op used).1,fun op used => (realizedSlot op used).2⟩

theorem assignmentFit (f ρ : Nat → Nat) (top : Nat) (ops : List LowerOperand)
    (ranked : StrictLower top ops) (live : Live f ρ ops) :
    PreparedTableTied f top ρ ops (assignment f ρ ops) := by
  intro j hj
  let op := ops[j]
  have used : op ∈ ops := List.getElem_mem hj
  obtain ⟨v,hit⟩ := live op used
  have chosen : assignment f ρ ops (j+1) = v := by
    change ((ops[j]?).bind (fun u => (lowerOperandRead f ρ u).join)).getD 0 = v
    rw [List.getElem?_eq_getElem hj]
    change ((some op).bind (fun u => (lowerOperandRead f ρ u).join)).getD 0 = v
    simp [hit,Option.join]
  refine ⟨ranked op used,(preparedTiedProjection.1 f ρ op _).mp ?_⟩
  rw [chosen]
  exact hit

theorem exactKeptActualRoute : ExactKeptActualRoute := by
  intro f ρ top qs
  constructor
  · rintro ⟨q,used,ν,tie,pass⟩
    exact ⟨q,(keepMember top qs q).mpr ⟨used,(tiedStrictLive f ρ top q.1 ν tie).1⟩,ν,tie,pass⟩
  · rintro ⟨q,used,pass⟩
    exact ⟨q,((keepMember top qs q).mp used).1,pass⟩

theorem exactLowerHoldsAtAssignment (f ρ : Nat → Nat) (top : Nat) (q : Packet)
    (ranked : StrictLower top q.1) (shape : Shape q) (positive : ∀ n ∈ q.2.variables, 0 < n) :
    LowerHolds f ρ top q ↔ Live f ρ q.1 ∧ q.2.eval (assignment f ρ q.1) := by
  constructor
  · rintro ⟨ν,tied,passes⟩
    have live := (tiedStrictLive f ρ top q.1 ν tied).2
    have canonical := assignmentFit f ρ top q.1 ranked live
    have agree (n : Nat) (used : n ∈ q.2.variables) : ν n = assignment f ρ q.1 n := by
      have pos := positive n used
      cases n with
      | zero => exact False.elim (Nat.lt_irrefl _ pos)
      | succ j =>
        have within : j < q.1.length := Nat.lt_of_succ_le (shape.2 (j+1) used)
        have first := (preparedTiedProjection.1 f ρ q.1[j] (ν (j+1))).mpr (tied j within).2
        have second := (preparedTiedProjection.1 f ρ q.1[j] (assignment f ρ q.1 (j+1))).mpr (canonical j within).2
        exact Option.some.inj (Option.some.inj (first.symm.trans second))
    exact ⟨live,(formula_eval_congr q.2 ν (assignment f ρ q.1) agree).mp passes⟩
  · rintro ⟨live,passes⟩
    exact ⟨assignment f ρ q.1,assignmentFit f ρ top q.1 ranked live,passes⟩

end LogicLineages.PermittedControl.ActualGreatestRouteResidual
