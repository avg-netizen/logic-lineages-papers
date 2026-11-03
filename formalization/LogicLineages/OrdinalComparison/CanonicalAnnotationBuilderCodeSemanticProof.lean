module
public import LogicLineages.OrdinalComparison.CanonicalAnnotationBuilderCodeTargets
public import LogicLineages.OrdinalComparison.SourceAnnotationBuilderProof
public import LogicLineages.OrdinalComparison.SourceAnnotationPartialCodeProof
public import LogicLineages.OrdinalComparison.TrackedSourceInspectionCodeProof
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.CanonicalAnnotationBuilderCode.Proof
open ScalarAnnotationData AdmissibleAssignment ActiveScalarAnnotation AdditiveHeadTree
open SourceFreeOccurrences AssignmentSupport SourceAnnotationBuilder SourceAnnotationBuilder.Proof

private theorem mod_tag (a tag : Nat) (h : tag < 8) : (8*a+tag)%8=tag := by omega
private theorem div_tag (a tag : Nat) (h : tag < 8) : (8*a+tag)/8=a := by omega

private theorem assignment_code {Γ τ} (t : OriginalTerm Γ τ) (u : OrdinalVector Γ τ.level)
    (hu : assignment OrdinalSyntax.defaultPolicy t = some u) :
    DefaultSourceAssignment.assignmentCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm t) =
      some (OrdinalSyntax.vectorCode u) := by
  rw [DefaultSourceAssignment.Proof.assignmentCorrect,hu,Option.map_some]

private theorem vector_zero {Γ m} (u : OrdinalVector Γ m) :
    (OrdinalSyntax.vectorCode u).getD 0 0 = OrdinalSyntax.typedCode (u 0) := by
  simp [OrdinalSyntax.vectorCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn]

private theorem vector_size {Γ m} (u : OrdinalVector (.ground :: Γ) m) :
    ((OrdinalSyntax.vectorCode u).map OrdinalSyntax.partialSize).sum =
      ((List.ofFn u).map ordinalPartialSize).sum := by
  simp only [OrdinalSyntax.vectorCode,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  exact OrdinalSyntax.ordinalSyntaxPartialSizeCorrect Γ .ground (u j)

private theorem inactive_result {k Γ F n} (e : TrackedSource.Expr k Γ F n)
    (hin : TrackedSource.active e = false) :
    ∃ (u : OrdinalVector Γ (Ty.curriedGround n).level) (d : Tree k Γ F),
      buildCode (Γ.map SyntaxCode.typeCode) (SourceTypedPorts.variableIndex F)
        (SyntaxCode.encodeTerm (TrackedSource.erase e)) = some (OrdinalSyntax.vectorCode u,SourceAnnotationCode.code d) ∧
      assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase e) = some u ∧ erase d=u 0 ∧ Valid d := by
  obtain ⟨u,hu,hg⟩ := actualAdmissibleAssignmentGenerated Γ (Ty.curriedGround n) OrdinalSyntax.defaultPolicy (TrackedSource.erase e)
  refine ⟨u,.free (u 0),?_,hu,rfl,hg 0,?_⟩
  · have hi := TrackedSourceInspectionCode.Proof.actualGrammarInspection k Γ F n e
    rw [buildCode.eq_def]
    dsimp only
    rw [hi.2.1]
    simp only [bind,pure,Option.bind_some]
    rw [hi.2.2,assignment_code _ u hu]
    simp only [bind,pure,Option.bind_some,hi.1,hin,↓reduceIte,vector_zero]
    rfl
  · intro ha
    have ht := (source_activity e u hu).mp ha
    rw [hin] at ht
    contradiction

theorem actualSourceBuild : Targets.ActualSourceBuild := by
  intro k Γ F n e
  induction e with
  | @tracked Γ F =>
    let u : OrdinalVector Γ (Ty.curriedGround (k+1)).level := fun j => .var ⟨_,F,j⟩
    have hu : assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase (TrackedSource.Expr.tracked (k := k) (F := F))) = some u := rfl
    refine ⟨u,.tracked,?_,hu,rfl,True.intro⟩
    have hi := TrackedSourceInspectionCode.Proof.actualGrammarInspection k Γ F (k+1) .tracked
    rw [buildCode.eq_def]
    dsimp only
    rw [hi.2.1]
    simp only [bind,pure,Option.bind_some]
    rw [hi.2.2,assignment_code _ u hu]
    simp only [bind,pure,Option.bind_some,hi.1,TrackedSource.active,Bool.true_eq_false,↓reduceIte]
    simp [TrackedSource.erase,SyntaxCode.encodeTerm,SyntaxCode.erase,SyntaxCode.code,
      SourceAnnotationCode.code]
  | @ground Γ F x => exact inactive_result (.ground x) rfl
  | @free Γ F n t hf => exact inactive_result (.free t hf) rfl
  | @app Γ F n f a ihf iha =>
    by_cases hin : TrackedSource.active (.app f a) = false
    · exact inactive_result (.app f a) hin
    have hactive : TrackedSource.active (.app f a) = true := Bool.eq_true_of_not_eq_false hin
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
    · have hi := TrackedSourceInspectionCode.Proof.actualGrammarInspection k Γ F n (.app f a)
      have harg := (SyntaxCode.Proof.typedCheckExact Γ .ground _).mpr ⟨TrackedSource.erase a,rfl⟩
      rw [buildCode.eq_def]
      dsimp only
      rw [hi.2.1]
      simp only [bind,pure,Option.bind_some]
      rw [hi.2.2,assignment_code _ u hu]
      simp only [bind,pure,Option.bind_some,hi.1,hactive,Bool.true_eq_false,↓reduceIte]
      simp only [TrackedSource.erase,SyntaxCode.encodeTerm,SyntaxCode.erase,SyntaxCode.code] at hbf hba harg ⊢
      simp only [mod_tag _ 5 (by decide),div_tag _ 5 (by decide),Nat.unpair_pair,
        show ¬(5:Nat)=0 by decide,true_or,↓reduceIte,↓reduceDIte,harg,SyntaxCode.typeCode,
        bind,pure,Option.bind_some]
      change (buildCode (Γ.map SyntaxCode.typeCode) (SourceTypedPorts.variableIndex F)
        (SyntaxCode.encodeTerm (TrackedSource.erase f))).bind (fun vf =>
          (buildCode (Γ.map SyntaxCode.typeCode) (SourceTypedPorts.variableIndex F)
            (SyntaxCode.encodeTerm (TrackedSource.erase a))).bind (fun va =>
              some (OrdinalSyntax.vectorCode u,appData n (SyntaxCode.encodeTerm (TrackedSource.erase f)) vf va))) = _
      simp only [SyntaxCode.encodeTerm,hbf,hba,Option.bind_some]
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
    by_cases hin : TrackedSource.active (.lam body) = false
    · exact inactive_result (.lam body) hin
    have hactive : TrackedSource.active (.lam body) = true := Bool.eq_true_of_not_eq_false hin
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
    · have hi := TrackedSourceInspectionCode.Proof.actualGrammarInspection k Γ F (n+1) (.lam body)
      have hpc := SourceAnnotationPartialCode.Proof.exactPartialCode k Γ F db
      rw [hpd] at hpc
      have hfactor := vector_size ub
      rw [buildCode.eq_def]
      dsimp only
      rw [hi.2.1]
      simp only [bind,pure,Option.bind_some]
      rw [hi.2.2,assignment_code _ u hu]
      simp only [bind,pure,Option.bind_some,hi.1,hactive,Bool.true_eq_false,↓reduceIte]
      simp only [TrackedSource.erase,SyntaxCode.encodeTerm,SyntaxCode.erase,SyntaxCode.code]
      simp only [mod_tag _ 6 (by decide),div_tag _ 6 (by decide),Nat.unpair_pair,
        show ¬(6:Nat)=0 by decide,show ¬(6:Nat)=5 by decide,↓reduceIte,↓reduceDIte,
        SyntaxCode.typeCode]
      have hbb' := hbb
      simp only [List.map_cons,SyntaxCode.typeCode,SourceTypedPorts.variableIndex,
        SyntaxCode.encodeTerm] at hbb'
      rw [hbb']
      simp only [bind,pure,Option.bind_some,lambdaData]
      simp only [SourceTypedPorts.variableIndex,Option.map_some] at hpc
      rw [hpc]
      simp only [bind,pure,Option.bind_some]
      rw [hfactor,SourceAnnotationCode.Proof.exactRepeat,
        SourceAnnotationCode.Proof.closeTree_correct]
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
end LogicLineages.OrdinalComparison.Source.CanonicalAnnotationBuilderCode.Proof
