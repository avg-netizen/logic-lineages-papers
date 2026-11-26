module
public import LogicLineages.PermittedControl.ActualGreatestRouteResidualTargets
import LogicLineages.PermittedControl.ActualGreatestRouteResidualTableProof
import LogicLineages.PermittedControl.ActualGreatestRouteResidualDecodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualGreatestRouteResidual
open ActualSelectedSignedRouteProjection (project LowerHolds)
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRoutePacket (Shape)
open OriginalMatrixLowDimension (dimension supportSet)

theorem exactActualLowerRouteFamily : ExactActualLowerRouteFamily := by
  intro f ρ top minimum qs shapes
  have one (q : Packet) (member : q ∈ keep top qs) :=
    let h := (keepMember top qs q).mp member
    exactDecodedActualResidual f ρ top minimum q (shapes q h.1) h.2
  have decomp (p : Residual) (used : p ∈ lowerFamily top minimum qs) :
      ∃ q ∈ keep top qs, decodeRoute minimum q = some p := List.mem_filterMap.mp used
  have atRoute (p : Residual) (q : Packet) (used : q ∈ keep top qs)
      (decoded : decodeRoute minimum q = some p) :
      (∀ rank ∈ supportSet (rows p), rank < top) ∧
      (LowerHolds f ρ top (project minimum q) ↔ LowerMatrix f ρ p) := by
    obtain ⟨other,old,_,_,ranked,exactValue⟩ := one q used
    have same := Option.some.inj (old.symm.trans decoded)
    subst p
    exact ⟨ranked,exactValue⟩
  refine ⟨?_,?_⟩
  · intro p used
    obtain ⟨q,kept,decoder⟩ := decomp p used
    exact (atRoute p q kept decoder).1
  constructor
  · rintro ⟨q,member,ν,tied,passes⟩
    have kept : q ∈ keep top qs :=
      (keepMember top qs q).mpr ⟨member,(tiedStrictLive f ρ top q.1 ν tied).1⟩
    obtain ⟨output,decoder,_,_,_,actual⟩ := one q kept
    exact ⟨output,List.mem_filterMap.mpr ⟨q,kept,decoder⟩,actual.mp ⟨ν,tied,passes⟩⟩
  · rintro ⟨p,used,truth⟩
    obtain ⟨q,kept,decoder⟩ := decomp p used
    exact ⟨q,((keepMember top qs q).mp kept).1,(atRoute p q kept decoder).2.mpr truth⟩

theorem exactActualLowerRouteDimension : ExactActualLowerRouteDimension := by
  intro top minimum qs source shapes dense p used
  have rank := (exactActualLowerRouteFamily (fun _ => 0) (fun _ => 0) top minimum qs shapes).1 p used
  have proper : supportSet (rows p) ⊆ (supportSet source).erase top := by
    intro k member
    have lower := rank k member
    exact Finset.mem_erase.mpr ⟨ne_of_lt lower,dense k lower.le⟩
  exact ⟨proper,(Finset.card_le_card proper).trans_lt (Finset.card_erase_lt_of_mem (dense top le_rfl))⟩

end LogicLineages.PermittedControl.ActualGreatestRouteResidual
