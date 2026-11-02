module
public import LogicLineages.OrdinalComparison.SourceAnnotationBuilderStructureProof
public import LogicLineages.OrdinalComparison.ScalarAnnotationDataProof
public import LogicLineages.OrdinalComparison.AdditiveHeadTreeProof
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportAssignmentProof
public import LogicLineages.OrdinalComparison.TrackedSourceProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAnnotationBuilder.Proof
open ScalarAnnotationData AdmissibleAssignment ActiveScalarAnnotation AdditiveHeadTree
open SourceFreeOccurrences AssignmentSupport

theorem source_activity {k Γ F n} (e : TrackedSource.Expr k Γ F n)
    (u : OrdinalVector Γ (Ty.curriedGround n).level)
    (hu : assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u) :
    Active F (u 0) ↔ TrackedSource.active e = true :=
  ((AssignmentSupport.Proof.assignment_support _ _ _ hu).2 ⟨_,F⟩).trans
    (TrackedSource.Proof.exactActivity k Γ F n e).symm

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

theorem abstraction_scalar {Γ m} (h : OrdinalVector (.ground :: Γ) m)
    (u : OrdinalVector Γ (max (Ty.ground.level+1) m)) (pt : OrdinalPartialVector Γ .ground)
    (hu : abstraction OrdinalSyntax.defaultPolicy h = some u)
    (hp : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (h 0) = some pt) :
    u 0 = .add (repeated OrdinalSyntax.defaultPolicy .scalarRepeat
      (2^(Ty.ground.level+1)*((List.ofFn h).map ordinalPartialSize).sum) (pt 0))
      (ordinalHeadClosure (h 0)) := by
  simp only [abstraction,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at hu
  obtain ⟨ps,hps,rfl⟩ := hu
  have hp' := AssignmentSupport.Proof.collect_success _ _ _ hps 0
  have he : ps 0 = pt := Option.some.inj (hp'.symm.trans hp)
  change (.add (repeated OrdinalSyntax.defaultPolicy .scalarRepeat _ (ps 0 0))
    (ordinalHeadClosure (h 0)) : OrdinalExpression Γ) = _
  rw [he]

theorem actualSourceData : Targets.ActualSourceData := by
  intro k Γ F n e
  induction e with
  | @tracked Γ F =>
    exact ⟨(fun j => .var ⟨_,F,j⟩),.tracked,rfl,rfl,rfl,True.intro⟩
  | @ground Γ F x =>
    let u : OrdinalVector Γ 0 := fun j => .var ⟨_,x,j⟩
    have hu : assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase (TrackedSource.Expr.ground (k := k) (F := F) x)) = some u := rfl
    refine ⟨u,.free (u 0),rfl,hu,rfl,GeneratedOrdinalGrade.var x 0,?_⟩
    intro ha
    have hh := (source_activity (.ground x) u hu).mp ha
    simp [TrackedSource.active] at hh
  | @free Γ F n t hf =>
    obtain ⟨u,hu,hg⟩ := actualAdmissibleAssignmentGenerated Γ (Ty.curriedGround n) OrdinalSyntax.defaultPolicy t
    refine ⟨u,.free (u 0),?_,hu,rfl,hg 0,?_⟩
    · simpa only [build,hu,bind,pure,Option.bind_some]
    · intro ha
      exact hf ((AssignmentSupport.Proof.assignment_support _ t u hu).1 0 _ ha)
  | @app Γ F n f a ihf iha =>
    obtain ⟨uf,df,hbf,huf,hedf,hdf⟩ := ihf
    obtain ⟨ua,da,hba,hua,heda,hda⟩ := iha
    let u := application (σ := .ground) (τ := Ty.curriedGround n) OrdinalSyntax.defaultPolicy uf ua
    let d : Tree k Γ F := .collapse ⟨n,TrackedSource.erase f,uf⟩ (.add df da)
    have hu : assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase (.app f a)) = some u := by
      change (assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase f)).bind
        (fun vf => (assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase a)).bind
          (fun va => some (application OrdinalSyntax.defaultPolicy vf va))) = some u
      rw [huf,hua]
      rfl
    refine ⟨u,d,?_,hu,?_,?_⟩
    · simp only [build,hbf,hba,bind,pure,Option.bind_some]
      rfl
    · change (.collapse (uf (UnaryCarrier.headIndex n)) (.add (erase df) (erase da)) : OrdinalExpression Γ) = _
      rw [hedf,heda]
      exact (application_scalar uf ua).symm
    · obtain ⟨uf',huf',ht,hpos⟩ := AdditiveHeadTree.Proof.actualSourceTrees k Γ F (n+1) OrdinalSyntax.defaultPolicy f
      have he : uf' = uf := Option.some.inj (huf'.symm.trans huf)
      subst uf'
      refine ⟨huf,hpos (UnaryCarrier.headIndex n) (by change 0 < 1;decide),?_,⟨hdf,hda⟩⟩
      intro hx
      have hs := AssignmentSupport.Proof.assignment_support OrdinalSyntax.defaultPolicy (TrackedSource.erase f) uf huf
      have hscalar := (hs.2 ⟨Ty.curriedGround (k+1),F⟩).mpr (hs.1 (UnaryCarrier.headIndex n) _ hx)
      change Active F (.add (erase df) (erase da))
      rw [hedf,heda]
      unfold Active
      rw [AssignmentSupport.Proof.names_add]
      exact List.mem_append_left _ hscalar
  | @lam Γ F n body ih =>
    obtain ⟨ub,db,hbb,hub,hedb,hdb⟩ := ih
    obtain ⟨u,hu,hg⟩ := actualAdmissibleAssignmentGenerated Γ (Ty.curriedGround (n+1))
      OrdinalSyntax.defaultPolicy (TrackedSource.erase (.lam body))
    have habs := hu
    change (assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase body)).bind
      (fun w => abstraction OrdinalSyntax.defaultPolicy w) = some u at habs
    rw [hub] at habs
    change abstraction OrdinalSyntax.defaultPolicy ub = some u at habs
    obtain ⟨pd,pt,hpd,hpt,hepd,hValid⟩ := ScalarAnnotationData.Proof.exactGroundPartial k Γ F db hdb
    rw [hedb] at hpt
    let factor := 2^(Ty.ground.level+1)*((List.ofFn ub).map ordinalPartialSize).sum
    let d : Tree k Γ F := .add (repeatTree factor pd) (ScalarAnnotationData.closeTree db)
    refine ⟨u,d,?_,hu,?_,?_⟩
    · simp only [build,hbb,bind,pure,Option.bind_some,habs,hpd]
      rfl
    · change (.add (erase (repeatTree factor pd)) (erase (ScalarAnnotationData.closeTree db)) : OrdinalExpression Γ) = _
      rw [repeat_erase,ScalarAnnotationData.Proof.close_erase,hepd,hedb]
      exact (abstraction_scalar ub u pt habs hpt).symm
    · have hsum : 0 < ((List.ofFn ub).map ordinalPartialSize).sum := by
        rw [List.ofFn_succ,List.map_cons,List.sum_cons]
        have := (actualTypedPartialSize Γ .ground (ub 0)).1
        omega
      have hf : 0 < factor := Nat.mul_pos (Nat.pow_pos (by decide)) hsum
      exact ⟨repeat_valid factor pd hf hValid,ScalarAnnotationData.Proof.close_valid db hdb⟩
end LogicLineages.OrdinalComparison.Source.SourceAnnotationBuilder.Proof
