module
public import LogicLineages.OrdinalComparison.SourceReserveLowerBoundTransportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceReserveLowerBound.Proof
open ScalarCarrierAccounting ActiveScalarAnnotation AdditiveHeadTree AdmissibleAssignment

theorem floor_one {k Γ F n} (e : TrackedSource.Expr k Γ F n) : 1 ≤ sourceFloor e := by
  unfold sourceFloor
  split <;> cases e <;> simp_all

theorem source_activity {k Γ F n} (e : TrackedSource.Expr k Γ F n)
    (u : OrdinalVector Γ (Ty.curriedGround n).level)
    (hu : assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u) :
    Active F (u 0) ↔ TrackedSource.active e = true := by
  exact ((AssignmentSupport.Proof.assignment_support _ _ _ hu).2 ⟨_,F⟩).trans
    (TrackedSource.Proof.exactActivity k Γ F n e).symm

theorem renamed_activity {k Γ Δ F n} (e : TrackedSource.Expr k Γ F n)
    (u : OrdinalVector Γ (Ty.curriedGround n).level)
    (r : Renaming Γ (Ty.curriedGround (k+1) :: Δ))
    (hi : ∀ τ, Function.Injective (fun x : Variable Γ τ => r x)) (hF : r F = .here)
    (hu : assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u) :
    Active (.here : Variable _ _) (ordinalExpressionRename r (u 0)) ↔ TrackedSource.active e = true := by
  have he := SelectedAccountPreparation.Proof.active_rename r hi F (u 0)
  rw [hF] at he
  exact he.trans (source_activity e u hu)

theorem inactive_source_bound {k Γ Δ F n} (e : TrackedSource.Expr k Γ F n)
    (u : OrdinalVector Γ (Ty.curriedGround n).level)
    (r : Renaming Γ (Ty.curriedGround (k+1) :: Δ))
    (hi : ∀ τ, Function.Injective (fun x : Variable Γ τ => r x)) (hF : r F = .here)
    (hu : assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u)
    (he : TrackedSource.active e = false) (xs : List Carrier) (c : Nat)
    (hac : Account (ordinalExpressionRename r (u 0)) xs c) : sourceFloor e ≤ reserve xs c := by
  have hn : ¬ Active (.here : Variable _ _) (ordinalExpressionRename r (u 0)) := by
    intro h; have := (renamed_activity e u r hi hF hu).mp h; simp [he] at this
  rw [inactive_reserve hn hac]
  simp [sourceFloor,he]

theorem ground_floor {k Γ F} (e : TrackedSource.Expr k Γ F 0)
    (ha : TrackedSource.active e = true) : 4 ≤ sourceFloor e := by
  cases e <;> simp_all [TrackedSource.active,sourceFloor]

theorem nonfinite_operator_floor {k Γ Δ F n}
    (e : TrackedSource.Expr k Γ F (n+1))
    (u : OrdinalVector Γ (Ty.curriedGround (n+1)).level) (r : Renaming Γ Δ)
    (hu : assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u)
    (ha : TrackedSource.active e = true)
    (hn : Ordinal.omega0 ≤ unitValue (ordinalExpressionRename r (u (UnaryCarrier.headIndex n)))) :
    4 ≤ sourceFloor e := by
  cases e with
  | tracked =>
    simp only [TrackedSource.erase,assignment,Option.some.injEq] at hu
    subst u
    have hh : unitValue (ordinalExpressionRename r
        ((fun i => (.var ⟨_,F,i⟩ : OrdinalExpression _)) (UnaryCarrier.headIndex _))) = 1 := rfl
    rw [hh] at hn
    exact False.elim ((not_le_of_gt Ordinal.one_lt_omega0) hn)
  | free t hf => simp [TrackedSource.active] at ha
  | app f a => simp [sourceFloor,ha]
  | lam b => simp [sourceFloor,ha]

theorem application_scalar {Γ n} (u : OrdinalVector Γ (Ty.curriedGround (n+1)).level)
    (a : OrdinalVector Γ 0) :
    application (σ := .ground) (τ := Ty.curriedGround n) OrdinalSyntax.defaultPolicy u a 0 =
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

theorem lifted_injective {Γ Δ} (r : Renaming Γ Δ)
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

theorem renamedSourceLowerBound : Targets.RenamedSourceLowerBound := by
  intro k Γ Δ F n e
  induction e generalizing Δ with
  | @tracked Γ F =>
    intro u r hi hF hu xs c hac
    simp only [TrackedSource.erase,assignment,Option.some.injEq] at hu
    subst u
    change Account (.var ⟨_,r F,0⟩) xs c at hac
    rw [hF] at hac
    have he := account_reserve_transfer hac Account.tracked
    simpa [sourceFloor,TrackedSource.active,reserve] using he.ge
  | @ground Γ F x =>
    intro u r hi hF hu xs c hac
    exact inactive_source_bound (.ground x) u r hi hF hu rfl xs c hac
  | @free Γ F n t hf =>
    intro u r hi hF hu xs c hac
    exact inactive_source_bound (.free t hf) u r hi hF hu rfl xs c hac
  | @app Γ F n f a ihf iha =>
    intro u r hi hF hu xs c hac
    by_cases he : TrackedSource.active (.app f a) = false
    · exact inactive_source_bound (.app f a) u r hi hF hu he xs c hac
    have hea : TrackedSource.active (.app f a) = true := Bool.eq_true_of_not_eq_false he
    have hwhole := (renamed_activity (.app f a) u r hi hF hu).mpr hea
    simp only [TrackedSource.erase,assignment,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hu
    obtain ⟨uf,huf,ua,hua,rfl⟩ := hu
    rw [application_scalar] at hac hwhole
    change Account (.collapse (ordinalExpressionRename r (uf (UnaryCarrier.headIndex n)))
      (.add (ordinalExpressionRename r (uf 0)) (ordinalExpressionRename r (ua 0)))) xs c at hac
    change Active (.here : Variable _ _) (.collapse (ordinalExpressionRename r (uf (UnaryCarrier.headIndex n)))
      (.add (ordinalExpressionRename r (uf 0)) (ordinalExpressionRename r (ua 0)))) at hwhole
    have htail : Active (.here : Variable _ _)
        (.add (ordinalExpressionRename r (uf 0)) (ordinalExpressionRename r (ua 0))) := by
      have hor : TrackedSource.active f = true ∨ TrackedSource.active a = true := by
        simpa only [TrackedSource.active,Bool.or_eq_true] using hea
      rcases hor with hf | ha
      · exact active_add_left _ _ _ ((renamed_activity f uf r hi hF huf).mpr hf)
      · unfold Active
        rw [AssignmentSupport.Proof.names_add]
        exact List.mem_append_right _ ((renamed_activity a ua r hi hF hua).mpr ha)
    obtain ⟨uf',huf',htf,hpf⟩ := AdditiveHeadTree.Proof.actualSourceTrees k Γ F (n+1)
      OrdinalSyntax.defaultPolicy f
    have heuf : uf' = uf := Option.some.inj (huf'.symm.trans huf)
    subst uf'
    have hhead := SelectedAccountPreparation.Proof.head_rename r hi F
      (hpf (UnaryCarrier.headIndex n) (by change 0 < 1; decide))
    rw [hF] at hhead
    have hnfsum : Ordinal.omega0 ≤ unitValue (ordinalExpressionRename r (uf (UnaryCarrier.headIndex n))) →
        5 ≤ sourceFloor f + sourceFloor a := by
      intro hn
      by_cases ha : TrackedSource.active a = true
      · have := ground_floor a ha
        have := floor_one f
        omega
      · have hf : TrackedSource.active f = true := by
          simpa [TrackedSource.active,ha] using hea
        have := nonfinite_operator_floor f uf r huf hf hn
        have := floor_one a
        omega
    have hb := application_bound _ _ _ hhead hwhole htail (sourceFloor f) (sourceFloor a)
      (floor_one f) (floor_one a) (ihf Δ uf r hi hF huf) (iha Δ ua r hi hF hua) hnfsum xs c hac
    simpa [sourceFloor,hea] using hb
  | @lam Γ F n body ih =>
    intro u r hi hF hu xs c hac
    by_cases he : TrackedSource.active (.lam body) = false
    · exact inactive_source_bound (.lam body) u r hi hF hu he xs c hac
    have hea : TrackedSource.active body = true := Bool.eq_true_of_not_eq_false he
    obtain ⟨ub,hub,hgrade⟩ := AdmissibleAssignment.actualAdmissibleAssignmentGenerated
      (.ground :: Γ) (Ty.curriedGround n) OrdinalSyntax.defaultPolicy (TrackedSource.erase body)
    change (assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase body)).bind
      (fun w => abstraction OrdinalSyntax.defaultPolicy w) = some u at hu
    rw [hub] at hu
    change abstraction OrdinalSyntax.defaultPolicy ub = some u at hu
    let r' : Renaming (.ground :: Γ) (Ty.curriedGround (k+1) :: .ground :: Δ) :=
      fun x => SelectedBinder.swap (Renaming.lift r x)
    have hir' : ∀ τ, Function.Injective (fun x : Variable (.ground :: Γ) τ => r' x) := by
      intro τ x y hxy
      apply lifted_injective r hi τ
      have hh := congrArg (fun z => SelectedBinder.swap z) hxy
      simpa only [r',SelectedBinder.Proof.swap_swap] using hh
    have hF' : r' (.there F) = .here := by
      change SelectedBinder.swap (.there (r F)) = .here
      rw [hF]
      rfl
    let h := SourceRenaming.renameVector (Renaming.lift r) ub
    have huv : abstraction OrdinalSyntax.defaultPolicy h = some (SourceRenaming.renameVector r u) := by
      rw [SourceRenaming.Proof.abstraction_natural,hu]
      rfl
    obtain ⟨ub',hub',ht,hp⟩ := AdditiveHeadTree.Proof.actualSourceTrees k (.ground :: Γ) (.there F) n
      OrdinalSyntax.defaultPolicy body
    have heub : ub' = ub := Option.some.inj (hub'.symm.trans hub)
    subst ub'
    obtain ⟨ub',hub',ha⟩ := ActiveScalarAnnotation.Proof.actualSourceAnnotation k (.ground :: Γ) (.there F) n
      OrdinalSyntax.defaultPolicy body
    have heub : ub' = ub := Option.some.inj (hub'.symm.trans hub)
    subst ub'
    have htree := SelectedAccountPreparation.Proof.scalar_rename (Renaming.lift r) (lifted_injective r hi)
      (.there F) ht
    have hann := SelectedAccountPreparation.Proof.annotation_rename (Renaming.lift r) (lifted_injective r hi)
      (.there F) OrdinalSyntax.defaultPolicy ha
    have hFlift : Renaming.lift (τ := Ty.ground) r (.there F) = .there (.here : Variable (Ty.curriedGround (k+1) :: Δ) _) := by
      change Variable.there (r F) = _
      rw [hF]
    rw [hFlift] at htree hann
    have hactive : Active (.there (.here : Variable (Ty.curriedGround (k+1) :: Δ) _)) (h 0) := by
      have hh := SelectedAccountPreparation.Proof.active_rename (Renaming.lift r) (lifted_injective r hi)
        (.there F) (ub 0)
      rw [hFlift] at hh
      exact hh.mpr ((source_activity body ub hub).mpr hea)
    have hprepare : GroundPartialCarrierTransport.before k [] Δ (h 0) =
        ordinalExpressionRename r' (ub 0) := by
      rw [GroundPartialCarrierTransport.Proof.before_adj_eq_swap]
      exact SelectedAccountPreparation.Proof.expression_rename_comp (Renaming.lift r) SelectedBinder.swap (ub 0)
    have htr' := SelectedAccountPreparation.Proof.scalar_rename r' hir' (.there F) ht
    have han' := SelectedAccountPreparation.Proof.annotation_rename r' hir' (.there F) OrdinalSyntax.defaultPolicy ha
    rw [hF'] at htr' han'
    obtain ⟨ys,d,v,hy,hv,hval⟩ := ScalarCarrierAccounting.Proof.exactAccounting k (.ground :: Δ)
      (ordinalExpressionRename r' (ub 0)) htr' han'
    have hbound := ih (.ground :: Δ) ub r' hir' hF' hub ys d hy
    have hlow : 1 ≤ reserve ys d := (floor_one body).trans hbound
    rw [← hprepare] at hy
    obtain ⟨zs,e,hz,hl⟩ := abstraction_reserve h (SourceRenaming.renameVector r u) huv htree hann hactive ys d hy hlow
    have hres := account_reserve_transfer hac hz
    rw [hres]
    simpa [sourceFloor,TrackedSource.active,hea] using hl
end LogicLineages.OrdinalComparison.Source.SourceReserveLowerBound.Proof
