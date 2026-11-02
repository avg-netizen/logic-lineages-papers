module
public import LogicLineages.OrdinalComparison.OriginalSecondBudgetSourceProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalSecondBudget.Proof
open AdmissibleAssignment

theorem functional_level_one (k : Nat) : (Ty.curriedGround (k+1)).level = 1 := by
  have hlo := (UnaryCarrier.headIndex k).isLt
  have hhi := AdditiveHeadTree.Proof.curried_level_bound (k+1)
  change 1 < (Ty.curriedGround (k+1)).level+1 at hlo
  omega

theorem abstraction_second (k : Nat) (Γ : List Ty)
    (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) 0)
    (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)))
    (B : OrdinalVector Γ (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level)
    (hv : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (u 0) = some v)
    (hB : abstraction OrdinalSyntax.defaultPolicy u = some B) :
    B (boxSecond k) = v (HeadFiniteSurplus.outputTwo k) := by
  have hu : u = (fun _ : Fin 1 => u 0) := by funext j;rw [Fin.eq_zero j]
  rw [hu] at hB
  unfold abstraction at hB
  simp only [collect,Fin.val_zero,hv,Option.bind_some] at hB
  have he := congrArg (fun w : OrdinalVector Γ (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level =>
    w (boxSecond k)) (Option.some.inj hB)
  simp [boxSecond,HeadFiniteSurplus.outputTwo,functional_level_one,
    OrdinalSyntax.defaultPolicy,OrdinalSyntax.defaultShape,OrdinalSyntax.leftShape,
    AdmissibleSum.expand,Fin.cases_zero,Ty.level] at he
  exact he.symm

theorem full_box_second (k : Nat) (Γ : List Ty)
    (B : OrdinalVector Γ (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level)
    (caller : OrdinalVector Γ (Ty.curriedGround (k+1)).level) :
    box OrdinalSyntax.defaultPolicy B caller (boxSecond k) = B (boxSecond k) := by
  change ordinalBoxPositive (Ty.curriedGround (k+1)).level (ordinalVectorAt B) (ordinalVectorAt caller) 2 = _
  rw [ordinalBoxPositive]
  split
  · have := functional_level_one k
    omega
  · unfold ordinalVectorAt
    have h2 : 2 < (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level+1 := (boxSecond k).isLt
    rw [dif_pos h2]
    rfl

theorem originalFullBoxBudget : Targets.OriginalFullBoxBudget := by
  intro k Γ P C ha
  obtain ⟨u,v,hu,hv,hbound,hvalue⟩ := actualSourceSecond k Γ 0 P
  obtain ⟨B,hB,hBg⟩ := actualAdmissibleAssignmentGenerated Γ
    (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground) OrdinalSyntax.defaultPolicy (.lam (TrackedSource.erase P))
  obtain ⟨caller,hcaller,hcg⟩ := actualAdmissibleAssignmentGenerated Γ
    (Ty.curriedGround (k+1)) OrdinalSyntax.defaultPolicy C
  have hb : 4 ≤ scalarSecond (u 0) := by
    have hfloor := SourceReserveLowerBound.Proof.ground_floor P ha
    have hh : (4 : Int) ≤ (scalarSecond (u 0) : Int) := hfloor.trans hbound
    exact_mod_cast hh
  have hab := hB
  change (assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase P)).bind
    (fun w => abstraction OrdinalSyntax.defaultPolicy w) = some B at hab
  rw [hu] at hab
  have he := abstraction_second k Γ u v B hv hab
  refine ⟨u,B,caller,scalarSecond (u 0),hu,hB,hcaller,rfl,hb,full_box_second k Γ B caller,?_⟩
  intro ν
  rw [he]
  exact hvalue ν
end LogicLineages.OrdinalComparison.Source.OriginalSecondBudget.Proof
