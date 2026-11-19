module
public import LogicLineages.ControlSensitivityCurrent.CurrentReserveBoundArithmeticProof
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportAssignmentProof
public import LogicLineages.OrdinalComparison.TrackedSourceProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentReserve

open LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open ActiveScalarAnnotation AdditiveHeadTree HeadFiniteSurplus AdmissibleSum AdmissibleAssignment
open SelectedAccountPreparation.Proof (selectedCertificates selected_injective)

theorem floorOne {k Γ F n} (e : TrackedSource.Expr k Γ F n) : 1 ≤ sourceFloor e := by
  unfold sourceFloor
  split <;> cases e <;> simp_all

theorem sourceActivity (p : Policy) {k Γ F n} (e : TrackedSource.Expr k Γ F n)
    (u : OrdinalVector Γ (Ty.curriedGround n).level)
    (hu : assignment p (TrackedSource.erase e) = some u) :
    Active F (u 0) ↔ TrackedSource.active e = true := by
  exact ((AssignmentSupport.Proof.assignment_support p _ _ hu).2 ⟨_,F⟩).trans
    (TrackedSource.Proof.exactActivity k Γ F n e).symm

private theorem renamedActivity (p : Policy) {k Γ Δ F n} (e : TrackedSource.Expr k Γ F n)
    (u : OrdinalVector Γ (Ty.curriedGround n).level)
    (r : Renaming Γ (Ty.curriedGround (k+1) :: Δ))
    (hi : ∀ τ, Function.Injective (fun x : Variable Γ τ => r x)) (hF : r F = .here)
    (hu : assignment p (TrackedSource.erase e) = some u) :
    Active (.here : Variable _ _) (ordinalExpressionRename r (u 0)) ↔ TrackedSource.active e = true := by
  have h := SelectedAccountPreparation.Proof.active_rename r hi F (u 0)
  rw [hF] at h
  exact h.trans (sourceActivity p e u hu)

private theorem inactiveSourceBound (p : Policy) (f : Nat → Nat) {k Γ Δ F n}
    (e : TrackedSource.Expr k Γ F n) (u : OrdinalVector Γ (Ty.curriedGround n).level)
    (r : Renaming Γ (Ty.curriedGround (k+1) :: Δ))
    (hi : ∀ τ, Function.Injective (fun x : Variable Γ τ => r x)) (hF : r F = .here)
    (hu : assignment p (TrackedSource.erase e) = some u)
    (he : TrackedSource.active e = false) (xs : List (Carrier p)) (c : Nat)
    (hac : Account p f (ordinalExpressionRename r (u 0)) xs c) : sourceFloor e ≤ reserve xs c := by
  have hn : ¬ Active (.here : Variable _ _) (ordinalExpressionRename r (u 0)) := by
    intro h
    have hs := (renamedActivity p e u r hi hF hu).1 h
    simp [he] at hs
  rw [inactiveReserve hac hn]
  simp [sourceFloor,he]

private theorem groundFloor {k Γ F} (e : TrackedSource.Expr k Γ F 0)
    (ha : TrackedSource.active e = true) : 4 ≤ sourceFloor e := by
  cases e <;> simp_all [TrackedSource.active,sourceFloor]

private theorem nonfiniteOperatorFloor (p : Policy) (f : Nat → Nat) {k Γ Δ F n}
    (e : TrackedSource.Expr k Γ F (n+1))
    (u : OrdinalVector Γ (Ty.curriedGround (n+1)).level) (r : Renaming Γ Δ)
    (hu : assignment p (TrackedSource.erase e) = some u)
    (ha : TrackedSource.active e = true)
    (hn : Ordinal.omega0 ≤ unitValue f (ordinalExpressionRename r (u (UnaryCarrier.headIndex n)))) :
    4 ≤ sourceFloor e := by
  cases e with
  | tracked =>
    simp only [TrackedSource.erase,assignment,Option.some.injEq] at hu
    subst u
    have hh : unitValue f (ordinalExpressionRename r
        ((fun i => (.var ⟨_,F,i⟩ : OrdinalExpression _)) (UnaryCarrier.headIndex _))) = 1 := by
      unfold unitValue
      rw [zeroUnits] <;> rfl
    rw [hh] at hn
    exact False.elim ((not_le_of_gt Ordinal.one_lt_omega0) hn)
  | free t hf => simp [TrackedSource.active] at ha
  | app a b => simp [sourceFloor,ha]
  | lam b => simp [sourceFloor,ha]

private theorem applicationScalar (p : Policy) {Γ n} (u : OrdinalVector Γ (Ty.curriedGround (n+1)).level)
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
    have h1 : 1 < (Ty.curriedGround (n+1)).level+1 := (UnaryCarrier.headIndex n).isLt
    rw [dif_pos h1]
    rfl

private theorem liftedInjective {Γ Δ} (r : Renaming Γ Δ)
    (hi : ∀ τ, Function.Injective (fun x : Variable Γ τ => r x)) (τ : Ty) :
    Function.Injective (fun x : Variable (.ground :: Γ) τ => Renaming.lift r x) := by
  intro x y he
  cases x with
  | here => cases y <;> simp_all [Renaming.lift]
  | there x => cases y with
    | here => simp [Renaming.lift] at he
    | there y =>
      have hxy : r x = r y := Variable.there.inj he
      exact congrArg Variable.there (hi _ hxy)

theorem renamedSourceFloor : CurrentReserveTargets.RenamedSourceFloor := by
  intro p f k Γ Δ F n e
  induction e generalizing Δ with
  | @tracked Γ F =>
    intro u r hi hF hu xs c hac
    simp only [TrackedSource.erase,assignment,Option.some.injEq] at hu
    subst u
    change Account p f (.var ⟨_,r F,0⟩) xs c at hac
    rw [hF] at hac
    have he := reserveDeterminacy hac .tracked
    simpa [sourceFloor,TrackedSource.active,reserve] using he.ge
  | @ground Γ F x =>
    intro u r hi hF hu xs c hac
    exact inactiveSourceBound p f (.ground x) u r hi hF hu rfl xs c hac
  | @free Γ F n t hf =>
    intro u r hi hF hu xs c hac
    exact inactiveSourceBound p f (.free t hf) u r hi hF hu rfl xs c hac
  | @app Γ F n a b iha ihb =>
    intro u r hi hF hu xs c hac
    by_cases he : TrackedSource.active (.app a b) = false
    · exact inactiveSourceBound p f (.app a b) u r hi hF hu he xs c hac
    have hea : TrackedSource.active (.app a b) = true := Bool.eq_true_of_not_eq_false he
    have hwhole := (renamedActivity p (.app a b) u r hi hF hu).2 hea
    simp only [TrackedSource.erase,assignment,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hu
    obtain ⟨ua,hua,ub,hub,rfl⟩ := hu
    rw [applicationScalar p] at hac hwhole
    change Account p f (.collapse (ordinalExpressionRename r (ua (UnaryCarrier.headIndex n)))
      (.add (ordinalExpressionRename r (ua 0)) (ordinalExpressionRename r (ub 0)))) xs c at hac
    change Active (.here : Variable _ _) (.collapse (ordinalExpressionRename r (ua (UnaryCarrier.headIndex n)))
      (.add (ordinalExpressionRename r (ua 0)) (ordinalExpressionRename r (ub 0)))) at hwhole
    have htail : Active (.here : Variable _ _)
        (.add (ordinalExpressionRename r (ua 0)) (ordinalExpressionRename r (ub 0))) := by
      have hor : TrackedSource.active a = true ∨ TrackedSource.active b = true := by
        simpa only [TrackedSource.active,Bool.or_eq_true] using hea
      apply (activeAdd .here _ _).2
      exact hor.elim (fun h => Or.inl ((renamedActivity p a ua r hi hF hua).2 h))
        (fun h => Or.inr ((renamedActivity p b ub r hi hF hub).2 h))
    obtain ⟨ua',hua',_,hpa⟩ := AdditiveHeadTree.Proof.actualSourceTrees k Γ F (n+1) p a
    have heu : ua' = ua := Option.some.inj (hua'.symm.trans hua)
    subst ua'
    have hhead := SelectedAccountPreparation.Proof.head_rename r hi F
      (hpa (UnaryCarrier.headIndex n) (by change 0 < 1; decide))
    rw [hF] at hhead
    have hnfsum : Ordinal.omega0 ≤ unitValue f (ordinalExpressionRename r (ua (UnaryCarrier.headIndex n))) →
        5 ≤ sourceFloor a + sourceFloor b := by
      intro hn
      by_cases hb : TrackedSource.active b = true
      · have := groundFloor b hb
        have := floorOne a
        omega
      · have ha : TrackedSource.active a = true := by simpa [TrackedSource.active,hb] using hea
        have := nonfiniteOperatorFloor p f a ua r hua ha hn
        have := floorOne b
        omega
    have hbound := applicationBound p f _ _ _ hhead hwhole htail (sourceFloor a) (sourceFloor b)
      (floorOne a) (floorOne b) (iha Δ ua r hi hF hua) (ihb Δ ub r hi hF hub) hnfsum xs c hac
    simpa [sourceFloor,hea] using hbound
  | @lam Γ F n body ih =>
    intro u r hi hF hu xs c hac
    by_cases he : TrackedSource.active (.lam body) = false
    · exact inactiveSourceBound p f (.lam body) u r hi hF hu he xs c hac
    have hea : TrackedSource.active body = true := Bool.eq_true_of_not_eq_false he
    obtain ⟨ub,hub,ht,ha⟩ := originalCertificates p k (.ground :: Γ) (.there F) n body
    change (assignment p (TrackedSource.erase body)).bind (fun w => abstraction p w) = some u at hu
    rw [hub] at hu
    change abstraction p ub = some u at hu
    let r' : Renaming (.ground :: Γ) (Ty.curriedGround (k+1) :: .ground :: Δ) :=
      fun x => SelectedBinder.swap (Renaming.lift r x)
    have hir' : ∀ τ, Function.Injective (fun x : Variable (.ground :: Γ) τ => r' x) := by
      intro τ x y hxy
      apply liftedInjective r hi τ
      have hh := congrArg (fun z => SelectedBinder.swap z) hxy
      simpa only [r',SelectedBinder.Proof.swap_swap] using hh
    have hF' : r' (.there F) = .here := by
      change SelectedBinder.swap (.there (r F)) = .here
      rw [hF]
      rfl
    let h := SourceRenaming.renameVector (Renaming.lift r) ub
    have huv : abstraction p h = some (SourceRenaming.renameVector r u) := by
      rw [SourceRenaming.Proof.abstraction_natural,hu]
      rfl
    have htree := SelectedAccountPreparation.Proof.scalar_rename (Renaming.lift r) (liftedInjective r hi)
      (.there F) ht
    have hann := SelectedAccountPreparation.Proof.annotation_rename (Renaming.lift r) (liftedInjective r hi)
      (.there F) p ha
    have hFlift : Renaming.lift (τ := Ty.ground) r (.there F) =
        .there (.here : Variable (Ty.curriedGround (k+1) :: Δ) _) := by
      change Variable.there (r F) = _
      rw [hF]
    rw [hFlift] at htree hann
    have hactive : Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Δ) _)) (h 0) := by
      have hh := SelectedAccountPreparation.Proof.active_rename (Renaming.lift r) (liftedInjective r hi)
        (.there F) (ub 0)
      rw [hFlift] at hh
      exact hh.2 ((sourceActivity p body ub hub).2 hea)
    have hprepare : before k [] Δ (h 0) = ordinalExpressionRename r' (ub 0) := by
      rw [beforeAdjEqSwap]
      exact SelectedAccountPreparation.Proof.expression_rename_comp (Renaming.lift r) SelectedBinder.swap (ub 0)
    have htr' := SelectedAccountPreparation.Proof.scalar_rename r' hir' (.there F) ht
    have han' := SelectedAccountPreparation.Proof.annotation_rename r' hir' (.there F) p ha
    rw [hF'] at htr' han'
    obtain ⟨ys,d,_,_,hy,_,_⟩ := exactAnnotatedAccounting p f k (.ground :: Δ)
      (ordinalExpressionRename r' (ub 0)) htr' han'
    have hbound := ih (.ground :: Δ) ub r' hir' hF' hub ys d hy
    have hlow : 1 ≤ reserve ys d := (floorOne body).trans hbound
    rw [← hprepare] at hy
    obtain ⟨zs,c',hz,hl⟩ := abstractionReserve p f h (SourceRenaming.renameVector r u)
      huv htree hann hactive ys d hy hlow
    have hRes := reserveDeterminacy hac hz
    rw [hRes]
    simpa [sourceFloor,TrackedSource.active,hea] using hl

private theorem nonbareFloor {k Γ} {F : Variable Γ (Ty.curriedGround (k+1))}
    {n : Nat} (e : TrackedSource.Expr k Γ F n)
    (ha : TrackedSource.active e = true)
    (hn : ¬ HEq (TrackedSource.erase e) (show OriginalTerm Γ (Ty.curriedGround (k+1)) from .var F)) :
    4 ≤ sourceFloor e := by
  cases e with
  | tracked => exact False.elim (hn HEq.rfl)
  | ground x => simp [TrackedSource.active] at ha
  | free a h => simp [TrackedSource.active] at ha
  | app a b => simp [sourceFloor,ha]
  | lam a => simp [sourceFloor,ha]

theorem actualSourceFloor : CurrentReserveTargets.ActualSourceFloor := by
  intro p f k left right n t σ F hGen
  obtain ⟨e,rfl⟩ := (TrackedSource.Proof.exactGrammar k (left ++ σ :: right) F n t).1 hGen
  obtain ⟨u,hu,ht,ha⟩ := originalCertificates p k (left ++ σ :: right) F n e
  let r : Renaming (left ++ σ :: right) (σ :: (left ++ right)) := SelectedBinder.moveToHead left right σ
  let q := ordinalExpressionRename r (u 0)
  have hsel := selectedCertificates k left right p (u 0)
  have ht' : ScalarTrees (.here : Variable (σ :: (left ++ right)) σ) q := hsel.2.1 ht
  have ha' : Annotated p (.here : Variable (σ :: (left ++ right)) σ) q := hsel.2.2 ha
  obtain ⟨xs,c,v,hs,hc,hv,hVal⟩ := exactAnnotatedAccounting p f k (left ++ right) q ht' ha'
  have hFloor := renamedSourceFloor p f k (left ++ σ :: right) (left ++ right) F n e u r
    (selected_injective left right σ) (SelectedBinder.Proof.to_selected left right σ) hu
  have hLB := hFloor xs c hc
  refine ⟨e,u,rfl,hu,preparedAssignment p left right _ u hu,ht',ha',xs,c,v,hs,hc,hv,
    (floorOne e).trans hLB,?_,hFloor,hVal⟩
  intro hAct hNB
  exact (nonbareFloor e hAct hNB).trans hLB

end LogicLineages.ControlSensitivityCurrent.CurrentReserve
