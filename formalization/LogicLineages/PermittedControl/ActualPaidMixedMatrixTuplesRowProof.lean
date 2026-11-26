module
public import LogicLineages.PermittedControl.ActualPaidMixedMatrixTuplesTargets
import LogicLineages.PermittedControl.ActualGreatestCongruenceRouteProof
import LogicLineages.PermittedControl.ActualPaidSignedRouteReplayProof
import LogicLineages.PermittedControl.ActualSelectedSignedRoutePacketProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPaidMixedMatrixTuples
open ActualPaidSignedRouteReplay (exactOriginalSignedRoutesAcrossReplay)
open ActualGreatestCongruenceRoute (exactGreatestCongruenceShape exactGreatestCongruencePacket)
open ActualSelectedSignedRoutePacket (Shape exactEmittedRouteFamily)
open ActualSignedRouteCartesian (rowPackets)
open ActualPreparedSlotAppend (Packet)
open ActualBoundedSignedRoutes (PacketHolds)
open ActualSyntaxChargeBudget (syntaxBudget)

theorem alternativesShape (f baseline : Nat → Nat) (r top z : Nat) (row : MixedRow) :
    ∀ p ∈ alternatives r top row, Shape p := by
  intro p used
  cases row with
  | signed row =>
    obtain ⟨route,member,rfl⟩ := List.mem_map.mp used
    exact (exactEmittedRouteFamily f baseline top z (syntaxBudget r row.source.terms)
      row.test row.positive row.source).1 route member
  | modular m s positive =>
    have eq := List.mem_singleton.mp used
    subst p
    exact exactGreatestCongruenceShape top m s positive

theorem exactPaidMixedRow : ExactPaidMixedRow := by
  intro f B selected r top baseline row setup z minimum
  cases row with
  | signed row =>
    have source := exactOriginalSignedRoutesAcrossReplay f B selected r top baseline row.source setup z
      minimum row.test row.positive
    have packet := (exactEmittedRouteFamily f baseline top z (syntaxBudget r row.source.terms)
      row.test row.positive row.source).2
    refine source.trans (packet.symm.trans ?_)
    constructor
    · rintro ⟨route,member,passes⟩
      exact ⟨_,List.mem_map.mpr ⟨route,member,rfl⟩,passes⟩
    · rintro ⟨p,used,passes⟩
      obtain ⟨route,member,rfl⟩ := List.mem_map.mp used
      exact ⟨route,member,passes⟩
  | modular m s positive =>
    refine (exactGreatestCongruencePacket f B selected baseline top m s setup z minimum positive).2.symm.trans ?_
    constructor
    · intro passes
      exact ⟨_,List.mem_singleton.mpr rfl,passes⟩
    · rintro ⟨p,h,passes⟩
      have eq := List.mem_singleton.mp h
      subst p
      exact passes

end LogicLineages.PermittedControl.ActualPaidMixedMatrixTuples
