module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationPartialCodeProof
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundBudgetBoxProof
public import LogicLineages.OrdinalComparison.TrackedSourceInspectionCodeStatementChecks
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotation

open LogicLineages.OrdinalComparison.Source
open AdmissibleSum ScalarAnnotationData ActiveScalarAnnotation AdditiveHeadTree
open AdmissibleAssignment SourceFreeOccurrences AssignmentSupport

private theorem modTag (a tag : Nat) (h : tag < 8) : (8*a+tag)%8=tag := by omega
private theorem divTag (a tag : Nat) (h : tag < 8) : (8*a+tag)/8=a := by omega

private theorem vectorSize {Γ m} (u : OrdinalVector (.ground :: Γ) m) :
    ((OrdinalSyntax.vectorCode u).map OrdinalSyntax.partialSize).sum =
      ((List.ofFn u).map ordinalPartialSize).sum := by
  simp only [OrdinalSyntax.vectorCode,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  exact OrdinalSyntax.ordinalSyntaxPartialSizeCorrect Γ .ground (u j)

private theorem typedInactive (p : Policy) {k Γ F n} (e : TrackedSource.Expr k Γ F n)
    (hin : TrackedSource.active e = false)
    (u : OrdinalVector Γ (Ty.curriedGround n).level)
    (hu : assignment p (TrackedSource.erase e) = some u) :
    build p e = some (u,.free (u 0)) := by
  cases e with
  | tracked => simp [TrackedSource.active] at hin
  | ground x =>
    simp only [TrackedSource.erase,assignment,Option.some.injEq] at hu
    subst u
    rfl
  | free t h =>
    change assignment p t = some u at hu
    simp [build,hu]
  | app a b => simp [build,hu,hin]
  | lam body => simp [build,hu,hin]

private theorem inactiveBuild (p : Policy) {k Γ F n} (e : TrackedSource.Expr k Γ F n)
    (hin : TrackedSource.active e = false) :
    ∃ (u : OrdinalVector Γ (Ty.curriedGround n).level) (d : Tree k Γ F),
      build p e = some (u,d) ∧
      assignment p (TrackedSource.erase e) = some u ∧ Valid p d ∧ erase d = u 0 ∧
      CurrentGroundAnnotationCode.buildCode p (Γ.map SyntaxCode.typeCode)
        (SourceTypedPorts.variableIndex F) (SyntaxCode.encodeTerm (TrackedSource.erase e)) =
          some (OrdinalSyntax.vectorCode u,SourceAnnotationCode.code d) := by
  obtain ⟨u,hu,hg⟩ := actualAdmissibleAssignmentGenerated Γ (Ty.curriedGround n) p (TrackedSource.erase e)
  refine ⟨u,.free (u 0),typedInactive p e hin u hu,hu,⟨hg 0,?_⟩,rfl,?_⟩
  · intro ha
    have h := (CurrentReserve.sourceActivity p e u hu).1 ha
    rw [hin] at h
    contradiction
  · have hi := TrackedSourceInspectionCode.Proof.actualGrammarInspection k Γ F n e
    rw [CurrentGroundAnnotationCode.buildCode.eq_def]
    dsimp only
    rw [hi.2.1]
    simp only [bind,pure,Option.bind_some]
    rw [hi.2.2,CurrentGroundBudget.assignmentCode p _ u hu]
    simp only [bind,pure,Option.bind_some,hi.1,hin,↓reduceIte,CurrentGroundBudget.vectorZero]
    rfl

theorem actualAnnotation : CurrentGroundAnnotationTargets.ActualAnnotation := by
  intro p k Γ F n e
  induction e with
  | @tracked Γ F =>
    let u : OrdinalVector Γ (Ty.curriedGround (k+1)).level := fun j => .var ⟨_,F,j⟩
    have hu : assignment p (TrackedSource.erase (TrackedSource.Expr.tracked (k := k) (F := F))) = some u := rfl
    refine ⟨u,.tracked,rfl,hu,True.intro,rfl,?_⟩
    have hi := TrackedSourceInspectionCode.Proof.actualGrammarInspection k Γ F (k+1) .tracked
    rw [CurrentGroundAnnotationCode.buildCode.eq_def]
    dsimp only
    rw [hi.2.1]
    simp only [bind,pure,Option.bind_some]
    rw [hi.2.2,CurrentGroundBudget.assignmentCode p _ u hu]
    simp only [bind,pure,Option.bind_some,hi.1,TrackedSource.active,Bool.true_eq_false,↓reduceIte]
    simp [TrackedSource.erase,SyntaxCode.encodeTerm,SyntaxCode.erase,SyntaxCode.code,SourceAnnotationCode.code]
  | @ground Γ F x => exact inactiveBuild p (.ground x) rfl
  | @free Γ F n t h => exact inactiveBuild p (.free t h) rfl
  | @app Γ F n a b iha ihb =>
    by_cases hin : TrackedSource.active (.app a b) = false
    · exact inactiveBuild p (.app a b) hin
    have ha : TrackedSource.active (.app a b) = true := Bool.eq_true_of_not_eq_false hin
    obtain ⟨ua,da,hba,hua,hda,hea,hra⟩ := iha
    obtain ⟨ub,db,hbb,hub,hdb,heb,hrb⟩ := ihb
    let u := application (σ := .ground) (τ := Ty.curriedGround n) p ua ub
    let d : Tree k Γ F := .collapse ⟨n,TrackedSource.erase a,ua⟩ (.add da db)
    have hu : assignment p (TrackedSource.erase (.app a b)) = some u := by
      change (assignment p (TrackedSource.erase a)).bind
        (fun va => (assignment p (TrackedSource.erase b)).bind
          (fun vb => some (application p va vb))) = some u
      rw [hua,hub]
      rfl
    refine ⟨u,d,?_,hu,?_,?_,?_⟩
    · simp only [build,hu,ha,hba,hbb,bind,pure,Option.bind_some,↓reduceIte]
      rfl
    · obtain ⟨u',hu',_,hpos⟩ := AdditiveHeadTree.Proof.actualSourceTrees k Γ F (n+1) p a
      have he : u' = ua := Option.some.inj (hu'.symm.trans hua)
      subst u'
      refine ⟨hua,hpos (UnaryCarrier.headIndex n) (by change 0 < 1;decide),?_,⟨hda,hdb⟩⟩
      intro hx
      have hs := AssignmentSupport.Proof.assignment_support p (TrackedSource.erase a) ua hua
      have hscalar := (hs.2 ⟨Ty.curriedGround (k+1),F⟩).2 (hs.1 (UnaryCarrier.headIndex n) _ hx)
      change Active F (.add (erase da) (erase db))
      rw [hea,heb]
      exact (CurrentReserve.activeAdd F _ _).2 (Or.inl hscalar)
    · change (.collapse (ua (UnaryCarrier.headIndex n)) (.add (erase da) (erase db)) : OrdinalExpression Γ) = _
      rw [hea,heb]
      exact (CurrentGroundBudget.applicationScalar p ua ub).symm
    · have hi := TrackedSourceInspectionCode.Proof.actualGrammarInspection k Γ F n (.app a b)
      have harg := (SyntaxCode.Proof.typedCheckExact Γ .ground _).2 ⟨TrackedSource.erase b,rfl⟩
      rw [CurrentGroundAnnotationCode.buildCode.eq_def]
      dsimp only
      rw [hi.2.1]
      simp only [bind,pure,Option.bind_some]
      rw [hi.2.2,CurrentGroundBudget.assignmentCode p _ u hu]
      simp only [bind,pure,Option.bind_some,hi.1,ha,Bool.true_eq_false,↓reduceIte]
      simp only [TrackedSource.erase,SyntaxCode.encodeTerm,SyntaxCode.erase,SyntaxCode.code] at hra hrb harg ⊢
      simp only [modTag _ 5 (by decide),divTag _ 5 (by decide),Nat.unpair_pair,
        show ¬(5:Nat)=0 by decide,true_or,↓reduceIte,↓reduceDIte,harg,SyntaxCode.typeCode,
        bind,pure,Option.bind_some]
      change (CurrentGroundAnnotationCode.buildCode p (Γ.map SyntaxCode.typeCode) (SourceTypedPorts.variableIndex F)
        (SyntaxCode.encodeTerm (TrackedSource.erase a))).bind (fun ra =>
          (CurrentGroundAnnotationCode.buildCode p (Γ.map SyntaxCode.typeCode) (SourceTypedPorts.variableIndex F)
            (SyntaxCode.encodeTerm (TrackedSource.erase b))).bind (fun rb =>
              some (OrdinalSyntax.vectorCode u,CanonicalAnnotationBuilderCode.appData n
                (SyntaxCode.encodeTerm (TrackedSource.erase a)) ra rb))) = _
      simp only [SyntaxCode.encodeTerm,hra,hrb,Option.bind_some]
      rfl
  | @lam Γ F n body ih =>
    by_cases hin : TrackedSource.active (.lam body) = false
    · exact inactiveBuild p (.lam body) hin
    have ha : TrackedSource.active (.lam body) = true := Bool.eq_true_of_not_eq_false hin
    obtain ⟨ub,db,hbb,hub,hdb,heb,hrb⟩ := ih
    obtain ⟨u,hu,_⟩ := actualAdmissibleAssignmentGenerated Γ (Ty.curriedGround (n+1))
      p (TrackedSource.erase (.lam body))
    have habs := hu
    change (assignment p (TrackedSource.erase body)).bind (fun w => abstraction p w) = some u at habs
    rw [hub] at habs
    have hAbs : abstraction p ub = some u := habs
    obtain ⟨pt,pd,hpt,hpd,hpe,hpv,_,hpr⟩ := actualGroundPartial p k Γ F db hdb
    have hRun : AdmissiblePartial.run p 0 (ub 0) = some pt := by rw [← heb]; exact hpt
    let factor := 2*((List.ofFn ub).map ordinalPartialSize).sum
    let d : Tree k Γ F := .add (repeatTree p pd factor) (closeTree db)
    refine ⟨u,d,?_,hu,?_,?_,?_⟩
    · simp only [build,hu,ha,hbb,hpd,bind,pure,Option.bind_some,↓reduceIte]
      rfl
    · have hpos : 0 < factor := Nat.mul_pos (by decide) (CurrentGroundBudget.sizeSumPositive ub)
      exact ⟨repeatValid p pd factor hpos hpv,closeValid p db hdb⟩
    · change (.add (erase (repeatTree p pd factor)) (erase (closeTree db)) : OrdinalExpression Γ) = _
      rw [repeatErase,ScalarAnnotationData.Proof.close_erase,hpe,heb]
      exact (CurrentGroundBudget.abstractionScalar p ub u pt hAbs hRun).symm
    · have hi := TrackedSourceInspectionCode.Proof.actualGrammarInspection k Γ F (n+1) (.lam body)
      rw [CurrentGroundAnnotationCode.buildCode.eq_def]
      dsimp only
      rw [hi.2.1]
      simp only [bind,pure,Option.bind_some]
      rw [hi.2.2,CurrentGroundBudget.assignmentCode p _ u hu]
      simp only [bind,pure,Option.bind_some,hi.1,ha,Bool.true_eq_false,↓reduceIte]
      simp only [TrackedSource.erase,SyntaxCode.encodeTerm,SyntaxCode.erase,SyntaxCode.code]
      simp only [modTag _ 6 (by decide),divTag _ 6 (by decide),Nat.unpair_pair,
        show ¬(6:Nat)=0 by decide,show ¬(6:Nat)=5 by decide,↓reduceIte,↓reduceDIte,
        SyntaxCode.typeCode]
      have hrb' := hrb
      simp only [List.map_cons,SyntaxCode.typeCode,SourceTypedPorts.variableIndex,SyntaxCode.encodeTerm] at hrb'
      rw [hrb']
      simp only [bind,pure,Option.bind_some,CurrentGroundAnnotationCode.lambdaData]
      change ((CurrentGroundAnnotationCode.groundPartialCode p _
        (SourceAnnotationCode.code db)).bind (fun pc =>
          (CurrentGroundAnnotationCode.repeatCode p (2*((OrdinalSyntax.vectorCode ub).map OrdinalSyntax.partialSize).sum) pc).bind
            (fun rc => some (4*Nat.pair rc (SourceAnnotationCode.closeCode (SourceAnnotationCode.code db))+2)))).bind
        (fun dc => some (OrdinalSyntax.vectorCode u,dc)) = _
      rw [hpr,Option.bind_some,vectorSize ub,markerExpansion.2 k Γ F p factor pd,
        Option.bind_some,Option.bind_some,SourceAnnotationCode.Proof.closeTree_correct]
      rfl

end LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotation
