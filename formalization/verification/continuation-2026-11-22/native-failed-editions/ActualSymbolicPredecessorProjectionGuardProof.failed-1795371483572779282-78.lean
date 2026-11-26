module
public import LogicLineages.PermittedControl.ActualSymbolicPredecessorProjectionTargets
import LogicLineages.PermittedControl.StableSortedHighFieldPacketProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSymbolicPredecessorProjection
open PreparedProjection
open StableSortedHighField (orderGuard orderGuardEval appendOrderShape)
open ActualSelectedSignedRoutePacket (Shape)
open ActualBoundedSignedRoutes (PacketHolds)

private theorem shape (top : Nat) : Shape (predecessorPacket top) := by
  change PreparedInput [.coordinate (top-1)] (orderGuard 1)
  constructor
  · intro a ha t used
    have singleton : a = .nonnegative (-1,[(1,.variable 0),(-1,.variable 1)]) := List.mem_singleton.mp ha
    subst a
    rcases List.mem_cons.mp used with first | tail
    · subst t; exact ⟨0,rfl⟩
    · have second := List.mem_singleton.mp tail
      subst t
      exact ⟨1,rfl⟩
  · intro n used
    change n ∈ [0,1] at used
    rcases List.mem_cons.mp used with first | tail
    · subst n; exact Nat.zero_le _
    · have second := List.mem_singleton.mp tail
      subst n
      exact le_rfl

theorem exactSymbolicPredecessorGuard : ExactSymbolicPredecessorGuard := by
  intro f baseline top z nonempty
  let pred := top-1
  let q := predecessorPacket top
  have genuine (ν : Nat → Nat) (tied : PreparedTableTied f top baseline q.1 ν) :
      ν 1 = baseline pred := (tied 0 (by decide)).2
  have interpret (ν : Nat → Nat) (tied : PreparedTableTied f top baseline q.1 ν) :
      q.2.eval (Function.update ν 0 z) ↔ baseline pred+1 ≤ z := by
    change (orderGuard 1).eval (Function.update ν 0 z) ↔ _
    rw [orderGuardEval,Function.update_self,Function.update_of_ne (by decide : (1 : Nat) ≠ 0),genuine ν tied]
    omega
  refine ⟨shape top,?_⟩
  constructor
  · rintro ⟨ν,tied,passed⟩
    exact (interpret ν tied).mp passed
  · intro bound
    let ν : Nat → Nat := fun _ => baseline pred
    have tied : PreparedTableTied f top baseline q.1 ν := by
      intro j used
      have unitIndex : j < 1 := used
      have ej : j = 0 := by omega
      subst j
      refine ⟨?_,rfl⟩
      change top-1 < top
      omega
    exact ⟨ν,tied,(interpret ν tied).mpr bound⟩

end LogicLineages.PermittedControl.ActualSymbolicPredecessorProjection
