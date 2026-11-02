module
public import LogicLineages.OrdinalComparison.GroundPartialCarrierTransportTargets
public import LogicLineages.OrdinalComparison.SelectedAccountPreparationProof
public import LogicLineages.OrdinalComparison.GroundCarrierTransportProof
public import LogicLineages.OrdinalComparison.AccountSemanticDeterminacyProof
public import LogicLineages.OrdinalComparison.ScalarPartialActivityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundPartialCarrierTransport.Proof
open ActiveScalarAnnotation ScalarCarrierAccounting AssignmentSupport SourceFreeOccurrences
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem before_adj_eq_swap (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.ground :: Ty.curriedGround (k+1) :: Γ)) :
    before k [] Γ q = ordinalExpressionRename
      (@SelectedBinder.swap Γ Ty.ground (Ty.curriedGround (k+1))) q := by
  induction q with
  | var c => rcases c with ⟨τ,x,j⟩; cases x with
    | here => rfl
    | there x => cases x <;> rfl
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    simp only [before,SelectedAccountPreparation.prepare,ordinalExpressionRename,substitute] at iha ihb ⊢
    rw [iha,ihb]
    rfl

theorem before_active (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.ground :: Ty.curriedGround (k+1) :: Γ)) :
    Active (.here : Variable (Ty.curriedGround (k+1) :: Ty.ground :: Γ) _) (before k [] Γ q) ↔
      Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q := by
  have ha := SelectedAccountPreparation.Proof.active_rename
    (SelectedBinder.moveToHead [Ty.ground] Γ (Ty.curriedGround (k+1)))
    (SelectedAccountPreparation.Proof.selected_injective [Ty.ground] Γ (Ty.curriedGround (k+1)))
    (SelectedBinder.selected [Ty.ground] Γ (Ty.curriedGround (k+1))) q
  rw [SelectedBinder.Proof.to_selected] at ha
  exact ha

theorem adjacentClosureCalibration : Targets.AdjacentClosureCalibration := by
  intro k Γ q
  have he : GroundClosing.expression (GroundClosing.GroundMap.lift (GroundOperatorDischarge.groundMap Γ))
      (before k [] Γ q) = ordinalHeadClosure q := by
    induction q with
    | var c => rcases c with ⟨τ,x,j⟩; cases x with
      | here => rfl
      | there x => cases x <;> rfl
    | zero | one | omega => rfl
    | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
      simp only [before,SelectedAccountPreparation.prepare,ordinalExpressionRename,
        GroundClosing.expression,ordinalHeadClosure,substitute] at iha ihb ⊢
      rw [iha,ihb]
  refine ⟨he,before_active k Γ q,?_,?_⟩
  · have hd := (GroundCarrierTransport.Proof.trackedInvariants k (Ty.ground :: Γ) Γ
      (GroundOperatorDischarge.groundMap Γ) (before k [] Γ q)).2.2
    rw [he] at hd
    exact hd
  · have hv := GroundCarrierTransport.Proof.exactUnitValue
      (Ty.curriedGround (k+1) :: Ty.ground :: Γ) (Ty.curriedGround (k+1) :: Γ)
      (GroundClosing.GroundMap.lift (GroundOperatorDischarge.groundMap Γ)) (before k [] Γ q)
    rw [he] at hv
    exact hv

theorem closure_account (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.ground :: Ty.curriedGround (k+1) :: Γ))
    (xs : List Carrier) (c : Nat) (ha : Account (before k [] Γ q) xs c) :
    Account (ordinalHeadClosure q) xs c := by
  have h := GroundCarrierTransport.Proof.exactAccountTransport k (Ty.ground :: Γ) Γ
    (GroundOperatorDischarge.groundMap Γ) (before k [] Γ q) xs c ha
  rw [(adjacentClosureCalibration k Γ q).1] at h
  exact h

theorem partial_active (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.ground :: Ty.curriedGround (k+1) :: Γ))
    (v : OrdinalPartialVector (Ty.curriedGround (k+1) :: Γ) Ty.ground)
    (hv : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 q = some v) :
    Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (v 0) ↔
      Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q := by
  change (⟨Ty.curriedGround (k+1),Variable.here⟩ : PackedVariable (Ty.curriedGround (k+1) :: Γ)) ∈ names (v 0) ↔ _
  exact (ScalarPartialActivity.Proof.exactScalarOldNames (Ty.curriedGround (k+1) :: Γ)
    Ty.ground OrdinalSyntax.defaultPolicy q v hv ⟨_,.here⟩).trans
    (TrackedSource.Proof.mem_dropBound (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (names q))

theorem inactive_account_data (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) (xs : List Carrier) (c : Nat)
    (ha : Account q xs c) (hn : ¬ Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q) :
    xs = [] ∧ c = 1 := by
  have hd := AccountSemanticDeterminacy.Proof.accountingDeterminacy k Γ q xs [] c 1 ha (.free hn)
  exact ⟨List.length_eq_zero_iff.mp hd.2.2.1,hd.2.1⟩

theorem inactive_transport (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.ground :: Ty.curriedGround (k+1) :: Γ))
    (xs : List Carrier) (c : Nat) (v : OrdinalPartialVector (Ty.curriedGround (k+1) :: Γ) Ty.ground)
    (hn : ¬ Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q)
    (ha : Account (before k [] Γ q) xs c)
    (hv : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 q = some v) :
    ∃ c', Account (v 0) xs c' ∧ c ≤ c' := by
  obtain ⟨rfl,rfl⟩ := inactive_account_data k (Ty.ground :: Γ) (before k [] Γ q) xs c ha
    (fun hh => hn ((before_active k Γ q).mp hh))
  exact ⟨1,.free (fun hh => hn ((partial_active k Γ q v hv).mp hh)),le_rfl⟩

theorem ground_free_transport (k : Nat) (Γ : List Ty)
    (q : OrdinalExpression (Ty.ground :: Ty.curriedGround (k+1) :: Γ))
    (xs : List Carrier) (c : Nat) (v : OrdinalPartialVector (Ty.curriedGround (k+1) :: Γ) Ty.ground)
    (ha : Account (before k [] Γ q) xs c) (hf : ordinalHeadFree q = true)
    (hv : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 q = some v) :
    ∃ c', Account (v 0) xs c' ∧ c ≤ c' := by
  by_cases hn : ¬ Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q
  · exact inactive_transport k Γ q xs c v hn ha hv
  · have hactive : Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) q :=
      Classical.byContradiction hn
    rw [AdmissiblePartial.run.eq_def,if_pos hf] at hv
    cases hv
    have hc := closure_account k Γ q xs c ha
    have hclosed := (ActiveScalarAnnotation.Proof.active_headClosure
      (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q).mpr hactive
    have hsum : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.add (ordinalHeadClosure q) .one) := by
      change _ ∈ names (.add _ _)
      rw [AssignmentSupport.Proof.names_add,List.mem_append]
      exact Or.inl hclosed
    have hone : Account (.one : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) [] 1 :=
      .free (by simp [Active,names,ordinalExpressionVariables])
    refine ⟨c+2,?_,by omega⟩
    change Account (.add (ordinalHeadClosure q) .one) xs (c+2)
    simpa only [List.append_nil,Nat.add_assoc] using Account.add hsum hc hone
end LogicLineages.OrdinalComparison.Source.GroundPartialCarrierTransport.Proof
