module
public import LogicLineages.OrdinalComparison.OriginalSecondBudgetCountProof
public import LogicLineages.OrdinalComparison.SourceReserveLowerBoundSourceProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalSecondBudget.Proof
open ActiveScalarAnnotation AdditiveHeadTree AdmissibleAssignment AdmissibleSum
open SourceReserveLowerBound

theorem active_not_free {k Γ} (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (ha : Active (.here : Variable _ _) q) : ordinalHeadFree q ≠ true := by
  intro hf
  exact ScalarCarrierAccounting.Proof.inactive_of_headFree q hf ha

/-- Literal copies are counted at the actual left-comb macro; no integer
reserve theorem is used for this independent second-output computation. -/
theorem left_repeat_count {k Γ}
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (ha : Active (.here : Variable _ _) q) (n : Nat) :
    Active (.here : Variable _ _) (expand (OrdinalSyntax.leftShape n) (fun _ => q)) ∧
    2*n+1 ≤ scalarSecond (expand (OrdinalSyntax.leftShape n) (fun _ => q)) := by
  induction n with
  | zero => exact ⟨ha,scalarSecond_pos q⟩
  | succ n ih =>
    have hac := SourceReserveLowerBound.Proof.active_add_left (.here : Variable _ _)
      (expand (OrdinalSyntax.leftShape n) (fun _ => q)) q ih.1
    refine ⟨hac,?_⟩
    change 2*(n+1)+1 ≤ scalarSecond (.add (expand (OrdinalSyntax.leftShape n) (fun _ => q)) q)
    rw [scalarSecond,if_neg (active_not_free _ hac)]
    have := scalarSecond_pos q
    omega

theorem repeated_count {k Γ} (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (ha : Active (.here : Variable _ _) q) (n : Nat) (hn : 2 ≤ n) :
    Active (.here : Variable _ _) (repeated OrdinalSyntax.defaultPolicy .scalarRepeat n q) ∧
    3 ≤ scalarSecond (repeated OrdinalSyntax.defaultPolicy .scalarRepeat n q) := by
  cases n with
  | zero => omega
  | succ n =>
    have h := left_repeat_count q ha n
    refine ⟨h.1,?_⟩
    change 3 ≤ scalarSecond (expand (OrdinalSyntax.leftShape n) (fun _ => q))
    omega

theorem abstraction_second_bound {k Γ m}
    (h : OrdinalVector (.ground :: Ty.curriedGround (k+1) :: Γ) m)
    (v : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (max (Ty.ground.level+1) m))
    (hv : abstraction OrdinalSyntax.defaultPolicy h = some v)
    (ha : Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) (h 0)) :
    5 ≤ scalarSecond (v 0) := by
  simp only [abstraction,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hv
  obtain ⟨ps,hps,rfl⟩ := hv
  have hp := AssignmentSupport.Proof.collect_success _ _ _ hps 0
  have hactive := (GroundPartialCarrierTransport.Proof.partial_active k Γ (h 0) (ps 0) hp).mpr ha
  let factor := 2^(Ty.ground.level+1)*((List.ofFn h).map ordinalPartialSize).sum
  have hsum : 0 < ((List.ofFn h).map ordinalPartialSize).sum := by
    rw [List.ofFn_succ,List.map_cons,List.sum_cons]
    have := (actualTypedPartialSize (Ty.curriedGround (k+1) :: Γ) Ty.ground (h 0)).1
    omega
  have hf : 2 ≤ factor := by dsimp [factor,Ty.level];omega
  have hr := repeated_count (ps 0 0) hactive factor hf
  have hw := SourceReserveLowerBound.Proof.active_add_left (.here : Variable _ _)
    (repeated OrdinalSyntax.defaultPolicy .scalarRepeat factor (ps 0 0)) (ordinalHeadClosure (h 0)) hr.1
  change 5 ≤ scalarSecond (.add
    (repeated OrdinalSyntax.defaultPolicy .scalarRepeat factor (ps 0 0)) (ordinalHeadClosure (h 0)))
  rw [scalarSecond,if_neg (active_not_free _ hw)]
  have := scalarSecond_pos (ordinalHeadClosure (h 0))
  omega

theorem source_second_bound {k Γ n}
    (e : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here n)
    (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround n).level)
    (hu : assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u) :
    sourceFloor e ≤ (scalarSecond (u 0) : Int) := by
  by_cases he : TrackedSource.active e = false
  · have hp := scalarSecond_pos (u 0)
    simp only [sourceFloor,he,Bool.false_eq_true,↓reduceIte]
    exact_mod_cast hp
  have hea : TrackedSource.active e = true := Bool.eq_true_of_not_eq_false he
  have hactive := (SourceReserveLowerBound.Proof.source_activity e u hu).mpr hea
  cases e with
  | tracked =>
    simp only [TrackedSource.erase,assignment,Option.some.injEq] at hu
    subst u
    simp [sourceFloor,TrackedSource.active,scalarSecond]
  | ground x => simp [TrackedSource.active] at hea
  | free t hf => simp [TrackedSource.active] at hea
  | @app Γ' F' n f a =>
    simp only [TrackedSource.erase,assignment,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hu
    obtain ⟨uf,huf,ua,hua,rfl⟩ := hu
    change OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (n+1)).level at uf
    change OrdinalVector (Ty.curriedGround (k+1) :: Γ) 0 at ua
    rw [SourceReserveLowerBound.Proof.application_scalar] at hactive ⊢
    have htail : Active (.here : Variable _ _) (.add (uf 0) (ua 0)) := by
      have hor : TrackedSource.active f = true ∨ TrackedSource.active a = true := by
        simpa only [TrackedSource.active,Bool.or_eq_true] using hea
      rcases hor with hf | ha
      · exact SourceReserveLowerBound.Proof.active_add_left _ _ _
          ((SourceReserveLowerBound.Proof.source_activity f uf huf).mpr hf)
      · unfold Active
        rw [AssignmentSupport.Proof.names_add]
        exact List.mem_append_right _ ((SourceReserveLowerBound.Proof.source_activity a ua hua).mpr ha)
    rw [scalarSecond,if_neg (active_not_free _ hactive),scalarSecond,if_neg (active_not_free _ htail)]
    have hh := HeadFiniteSurplus.Proof.secondCount_positive (uf (UnaryCarrier.headIndex n))
    have hf := scalarSecond_pos (uf 0)
    have ha := scalarSecond_pos (ua 0)
    have hb : 4 ≤ HeadFiniteSurplus.secondCount (uf (UnaryCarrier.headIndex n)) +
        (scalarSecond (uf 0) + scalarSecond (ua 0) + 1) := by omega
    simpa [sourceFloor,hea] using (show (4 : Int) ≤ _ from by exact_mod_cast hb)
  | @lam Γ' F' n body =>
    obtain ⟨ub,hub,hgrade⟩ := AdmissibleAssignment.actualAdmissibleAssignmentGenerated
      (.ground :: Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround n)
      OrdinalSyntax.defaultPolicy (TrackedSource.erase body)
    change (assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase body)).bind
      (fun w => abstraction OrdinalSyntax.defaultPolicy w) = some u at hu
    rw [hub] at hu
    have hb : TrackedSource.active body = true := hea
    have ha := (SourceReserveLowerBound.Proof.source_activity body ub hub).mpr hb
    have hbound := abstraction_second_bound ub u hu ha
    simpa [sourceFloor,TrackedSource.active,hb] using
      (show (5 : Int) ≤ (scalarSecond (u 0) : Int) from by exact_mod_cast hbound)

theorem actualSourceSecond : Targets.ActualSourceSecond := by
  intro k Γ n e
  obtain ⟨u,hu,ht,hpos⟩ := AdditiveHeadTree.Proof.actualSourceTrees k
    (Ty.curriedGround (k+1) :: Γ) .here n OrdinalSyntax.defaultPolicy e
  obtain ⟨v,hv,hc,hvalue⟩ := exactScalarSecond k Γ (u 0) ht
  exact ⟨u,v,hu,hv,source_second_bound e u hu,hvalue⟩
end LogicLineages.OrdinalComparison.Source.OriginalSecondBudget.Proof
