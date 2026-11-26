module
public import LogicLineages.PermittedControl.ActualSelectedSignedRouteProjectionTargets
import LogicLineages.PermittedControl.ActualSelectedSignedRoutePacketFoldProof
import LogicLineages.PermittedControl.PreparedParameterActualProof
import LogicLineages.PermittedControl.PreparedParameterOutputProof
import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaShapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSelectedSignedRouteProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection
open ActualPreparedSlotAppend (Packet append)
open ActualSelectedSignedRoutePacket (Shape exactRouteAppend)
open ActualBoundedSignedRoutes (PacketHolds)
open OriginalMatrixLinearRowFormula (safeAtom)

private theorem cutoffShape (minimum : Nat) : Shape (cutoffPacket minimum) := by
  change PreparedInput [] (.atom (.nonnegative (-(minimum : Int),[(1,.variable 0)])))
  apply safeAtom
  · intro t used
    have eq := List.mem_singleton.mp used
    subst t
    exact ⟨0,rfl⟩
  · intro n used
    change n ∈ [0] at used
    have eq := List.mem_singleton.mp used
    subst n
    exact Nat.le_refl 0

private theorem cutoffMeaning (f baseline : Nat → Nat) (top minimum z : Nat) :
    PacketHolds f baseline top z (cutoffPacket minimum) ↔ minimum ≤ z := by
  have exactBound (ν : Nat → Nat) :
      ((cutoffPacket minimum).2.eval (Function.update ν 0 z)) ↔ minimum ≤ z := by
    change 0 ≤ -(minimum : Int) + (1 * (Function.update ν 0 z 0 : Int) + 0) ↔ _
    simp only [one_mul,add_zero,Function.update_self]
    omega
  constructor
  · rintro ⟨ν,_,holds⟩; exact (exactBound ν).mp holds
  · intro below
    exact ⟨fun _ => 0,fun j hj => False.elim (Nat.not_lt_zero j hj),(exactBound _).mpr below⟩

theorem exactChosenRouteProjection : ExactChosenRouteProjection := by
  intro f baseline top minimum p shape
  let q := bounded minimum p
  have assembled (z : Nat) : Shape q ∧
      (PacketHolds f baseline top z q ↔ minimum ≤ z ∧ PacketHolds f baseline top z p) := by
    have out := exactRouteAppend f baseline top z (cutoffPacket minimum) p (cutoffShape minimum) shape
    exact ⟨out.1,out.2.trans (and_congr (cutoffMeaning f baseline top minimum z) Iff.rfl)⟩
  have ready := (assembled 0).1
  have outline := preparedProjectionSyntax q.1 q.2 ready
  refine ⟨rfl,⟨outline.2.1,fun n used => (outline.2.2.2 n used).2⟩,
    fun n used => (outline.2.2.2 n used).1,?_⟩
  constructor
  · rintro ⟨ν,tied,passes⟩
    obtain ⟨z,values⟩ := (preparedProjectionActual q.1 q.2 ready ν).mp passes
    exact ⟨z,(assembled z).2.mp ⟨ν,tied,values⟩⟩
  · rintro ⟨z,below,passes⟩
    obtain ⟨ν,tied,values⟩ := (assembled z).2.mpr ⟨below,passes⟩
    exact ⟨ν,tied,(preparedProjectionActual q.1 q.2 ready ν).mpr ⟨z,values⟩⟩

end LogicLineages.PermittedControl.ActualSelectedSignedRouteProjection
