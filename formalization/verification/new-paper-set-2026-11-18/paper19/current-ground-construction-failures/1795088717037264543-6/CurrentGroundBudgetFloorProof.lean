module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundBudgetCountProof
public import LogicLineages.ControlSensitivityCurrent.CurrentReserveSourceFloorProof
public import LogicLineages.OrdinalComparison.ScalarPartialActivityPartialProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundBudget

open LogicLineages.OrdinalComparison.Source
open AdmissibleSum AdmissibleAssignment AdditiveHeadTree ActiveScalarAnnotation
open OriginalSecondBudget
open CurrentReserve (sourceActivity activeAdd activeNotHeadFree)
open SourceFreeOccurrences

theorem applicationScalar (p : Policy) {Γ n} (u : OrdinalVector Γ (Ty.curriedGround (n+1)).level)
    (a : OrdinalVector Γ 0) :
    application (σ := .ground) (τ := Ty.curriedGround n) p u a 0 =
      .collapse (u (UnaryCarrier.headIndex n)) (.add (u 0) (a 0)) := by
  change (.collapse (ordinalBoxPositive 0 (ordinalVectorAt u) (ordinalVectorAt a) 1)
    (.add (u 0) (a 0)) : OrdinalExpression Γ) = _
  congr 1
  rw [ordinalBoxPositive]
  split
  · omega
  · unfold ordinalVectorAt
    rw [dif_pos (UnaryCarrier.headIndex n).isLt]
    rfl

theorem abstractionScalar (p : Policy) {Γ m} (h : OrdinalVector (.ground :: Γ) m)
    (u : OrdinalVector Γ (max (Ty.ground.level+1) m)) (pt : OrdinalPartialVector Γ .ground)
    (hu : abstraction p h = some u) (hp : AdmissiblePartial.run p 0 (h 0) = some pt) :
    u 0 = .add (repeated p .scalarRepeat
      (2*((List.ofFn h).map ordinalPartialSize).sum) (pt 0)) (ordinalHeadClosure (h 0)) := by
  simp only [abstraction,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hu
  obtain ⟨ps,hps,rfl⟩ := hu
  have hrun := AssignmentSupport.Proof.collect_success _ _ _ hps 0
  have he : ps 0 = pt := Option.some.inj (hrun.symm.trans hp)
  change (.add (repeated p .scalarRepeat _ (ps 0 0))
    (ordinalHeadClosure (h 0)) : OrdinalExpression Γ) = _
  rw [he]

theorem groundPartialActivity (p : Policy) {k Γ}
    (F : Variable Γ (Ty.curriedGround (k+1))) (q : OrdinalExpression (.ground :: Γ))
    (v : OrdinalPartialVector Γ .ground) (hv : AdmissiblePartial.run p 0 q = some v) :
    Active F (v 0) ↔ Active (.there F) q :=
  (ScalarPartialActivity.Proof.exactScalarOldNames Γ .ground p q v hv ⟨_,F⟩).trans
    (TrackedSource.Proof.mem_dropBound F (AssignmentSupport.names q))

private theorem shapeCount {k Γ} (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (ha : Active (.here : Variable _ _) q) {n : Nat} (s : Shape n) :
    0 < n ∧ Active (.here : Variable _ _) (expand s (fun _ => q)) ∧
      2*n ≤ scalarSecond (expand s (fun _ => q)) + 1 := by
  induction s with
  | leaf =>
    have h := OriginalSecondBudget.Proof.scalarSecond_pos q
    exact ⟨by decide,ha,by change 2 ≤ scalarSecond q + 1; omega⟩
  | @join n m a b iha ihb =>
    rcases iha with ⟨hn,ha',hca⟩
    rcases ihb with ⟨hm,hb',hcb⟩
    have hab := (activeAdd .here (expand a (fun _ => q)) (expand b (fun _ => q))).2 (Or.inl ha')
    refine ⟨by omega,hab,?_⟩
    change 2*(n+m) ≤ scalarSecond (.add (expand a (fun _ => q)) (expand b (fun _ => q))) + 1
    rw [scalarSecond,if_neg (activeNotHeadFree hab)]
    omega

private theorem repeatedCount (p : Policy) {k Γ} (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (ha : Active (.here : Variable _ _) q) (n : Nat) (hn : 2 ≤ n) :
    Active (.here : Variable _ _) (repeated p .scalarRepeat n q) ∧
      3 ≤ scalarSecond (repeated p .scalarRepeat n q) := by
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨_,hh,hc⟩ := shapeCount q ha (p.shape .scalarRepeat n)
    exact ⟨hh,by change 3 ≤ scalarSecond (expand (p.shape .scalarRepeat n) (fun _ => q)); omega⟩

theorem sizeSumPositive {Γ m} (h : OrdinalVector (.ground :: Γ) m) :
    0 < ((List.ofFn h).map ordinalPartialSize).sum := by
  rw [List.ofFn_succ,List.map_cons,List.sum_cons]
  have := (actualTypedPartialSize Γ .ground (h 0)).1
  omega

private theorem abstractionCount (p : Policy) {k Γ m}
    (h : OrdinalVector (.ground :: Ty.curriedGround (k+1) :: Γ) m)
    (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (max (Ty.ground.level+1) m))
    (hv : abstraction p h = some u)
    (ha : Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)) (h 0)) :
    5 ≤ scalarSecond (u 0) := by
  have hv' := hv
  simp only [abstraction,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hv'
  obtain ⟨ps,hps,_⟩ := hv'
  have hp := AssignmentSupport.Proof.collect_success _ _ _ hps 0
  have hp' : AdmissiblePartial.run p 0 (h 0) = some (ps 0) := hp
  have hactive := (groundPartialActivity p (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (h 0) (ps 0) hp').2 ha
  let factor := 2*((List.ofFn h).map ordinalPartialSize).sum
  have hfactor : 2 ≤ factor := by dsimp [factor]; have := sizeSumPositive h; omega
  have hrep := repeatedCount p (ps 0 0) hactive factor hfactor
  rw [abstractionScalar p h u (ps 0) hv hp']
  change 5 ≤ scalarSecond (.add (repeated p .scalarRepeat factor (ps 0 0)) (ordinalHeadClosure (h 0)))
  have hw := (activeAdd .here _ _).2 (Or.inl hrep.1)
  rw [scalarSecond,if_neg (activeNotHeadFree hw)]
  have hc := hrep.2
  have hd := OriginalSecondBudget.Proof.scalarSecond_pos (ordinalHeadClosure (h 0))
  omega

theorem sourceCountBound (p : Policy) {k Γ n}
    (e : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here n)
    (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround n).level)
    (hu : assignment p (TrackedSource.erase e) = some u) :
    CurrentReserve.sourceFloor e ≤ (scalarSecond (u 0) : Int) := by
  by_cases he : TrackedSource.active e = false
  · have hp : (1 : Int) ≤ (scalarSecond (u 0) : Int) := by exact_mod_cast
      OriginalSecondBudget.Proof.scalarSecond_pos (u 0)
    simpa [CurrentReserve.sourceFloor,he] using hp
  have hea : TrackedSource.active e = true := Bool.eq_true_of_not_eq_false he
  have hactive := (sourceActivity p e u hu).2 hea
  cases e with
  | tracked =>
    simp only [TrackedSource.erase,assignment,Option.some.injEq] at hu
    subst u
    simp [CurrentReserve.sourceFloor,TrackedSource.active,scalarSecond]
  | ground x => simp [TrackedSource.active] at hea
  | free t _ => simp [TrackedSource.active] at hea
  | @app Γ' F' n f a =>
    simp only [TrackedSource.erase,assignment,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hu
    obtain ⟨uf,huf,ua,hua,rfl⟩ := hu
    change OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (n+1)).level at uf
    change OrdinalVector (Ty.curriedGround (k+1) :: Γ) 0 at ua
    rw [applicationScalar p] at hactive ⊢
    have hor : TrackedSource.active f = true ∨ TrackedSource.active a = true := by
      simpa only [TrackedSource.active,Bool.or_eq_true] using hea
    have htail : Active (.here : Variable _ _) (.add (uf 0) (ua 0)) :=
      (activeAdd .here _ _).2 (hor.elim
        (fun hf => Or.inl ((sourceActivity p f uf huf).2 hf))
        (fun ha => Or.inr ((sourceActivity p a ua hua).2 ha)))
    rw [scalarSecond,if_neg (activeNotHeadFree hactive),scalarSecond,if_neg (activeNotHeadFree htail)]
    have hh := HeadFiniteSurplus.Proof.secondCount_positive (uf (UnaryCarrier.headIndex n))
    have hf := OriginalSecondBudget.Proof.scalarSecond_pos (uf 0)
    have ha := OriginalSecondBudget.Proof.scalarSecond_pos (ua 0)
    have hn : 4 ≤ HeadFiniteSurplus.secondCount (uf (UnaryCarrier.headIndex n)) +
        (scalarSecond (uf 0) + scalarSecond (ua 0) + 1) := by omega
    simpa [CurrentReserve.sourceFloor,hea] using (show (4 : Int) ≤ _ from by exact_mod_cast hn)
  | @lam Γ' F' n body =>
    obtain ⟨ub,hub,_⟩ := actualAdmissibleAssignmentGenerated
      (.ground :: Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround n) p (TrackedSource.erase body)
    change (assignment p (TrackedSource.erase body)).bind (fun w => abstraction p w) = some u at hu
    rw [hub] at hu
    have hab : abstraction p ub = some u := hu
    have hb : TrackedSource.active body = true := hea
    have ha := (sourceActivity p body ub hub).2 hb
    have h := abstractionCount p ub u hab ha
    simpa [CurrentReserve.sourceFloor,TrackedSource.active,hb] using
      (show (5 : Int) ≤ (scalarSecond (u 0) : Int) from by exact_mod_cast h)

theorem sourceSecondFloor : CurrentGroundBudgetTargets.SourceSecondFloor := by
  intro p k Γ n e
  obtain ⟨u,hu,ht,_⟩ := AdditiveHeadTree.Proof.actualSourceTrees k
    (Ty.curriedGround (k+1) :: Γ) .here n p e
  obtain ⟨v,hv,_,hval⟩ := exactScalarSecond p k Γ (u 0) ht
  exact ⟨u,v,hu,hv,sourceCountBound p e u hu,hval⟩

theorem groundSourceFloor {k Γ F} (P : TrackedSource.Expr k Γ F 0)
    (ha : TrackedSource.active P = true) : 4 ≤ CurrentReserve.sourceFloor P := by
  cases P with
  | ground x => simp [TrackedSource.active] at ha
  | free t hf => simp [TrackedSource.active] at ha
  | app a b => simp [CurrentReserve.sourceFloor,ha]

end LogicLineages.ControlSensitivityCurrent.CurrentGroundBudget
