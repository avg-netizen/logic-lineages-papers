module
public import LogicLineages.OrdinalComparison.SourceAnnotationCodeFoldProof
public import LogicLineages.OrdinalComparison.SourceCarrierMapCodeSemanticProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAnnotationCode.Proof
open ScalarAnnotationData

theorem exactOperatorCodec : Targets.ExactOperatorCodec := by
  intro Γ op
  have hv : operatorVector (operatorCode op) = OrdinalSyntax.vectorCode op.vector := by
    simp [operatorVector,operatorCode,Encodable.encodek]
  refine ⟨by simp [operatorArity,operatorCode],by simp [operatorSource,operatorCode],hv,?_⟩
  unfold operatorHead
  rw [hv]
  have hi : 1 < (Ty.curriedGround (op.arity+1)).level+1 := (UnaryCarrier.headIndex op.arity).isLt
  simp [OrdinalSyntax.vectorCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,
    Operator.head,UnaryCarrier.headIndex]

theorem exactErasure : Targets.ExactErasure := by
  intro k Γ F d
  induction d with
  | free q => simp [code,eraseCode,fold_free,erase]
  | tracked =>
    simp [code,eraseCode,fold_tracked,erase,OrdinalSyntax.typedCode,OrdinalSyntax.code,
      OrdinalSyntax.componentCode]
  | add a b iha ihb =>
    simp only [code,eraseCode,fold_add] at iha ihb ⊢
    rw [iha,ihb]
    rfl
  | collapse op tail ih =>
    simp only [code,eraseCode,fold_collapse] at ih ⊢
    rw [(exactOperatorCodec Γ op).2.2.2,ih]
    rfl

private theorem repeatTail_correct {k Γ F} (d : Tree k Γ F) (n : Nat) :
    repeatTail (code d) n = code (SourceAnnotationBuilder.repeatTail d n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [repeatTail,SourceAnnotationBuilder.repeatTail,code,ih]

theorem exactRepeat : Targets.ExactRepeat := by
  intro k Γ F count d
  cases count with
  | zero => rfl
  | succ n => exact repeatTail_correct d n

theorem closeOperator_correct {Γ} (op : Operator (.ground :: Γ)) :
    closeOperatorCode (operatorCode op) = operatorCode (closeOperator op) := by
  have hc := exactOperatorCodec (.ground :: Γ) op
  have hv : (OrdinalSyntax.vectorCode op.vector).map OrdinalSyntax.headClosure =
      OrdinalSyntax.vectorCode (closeOperator op).vector := by
    simp only [OrdinalSyntax.vectorCode,List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    exact OrdinalSyntax.ordinalSyntaxHeadClosureCorrect Γ .ground (op.vector j)
  unfold closeOperatorCode
  rw [hc.1,hc.2.1,hc.2.2.1,
    SourceCarrierMapCode.Proof.concreteExact.1 Γ _ op.source,hv]
  rfl

theorem closeTree_correct {k Γ} {F : Variable Γ (Ty.curriedGround (k+1))}
    (d : Tree k (.ground :: Γ) (.there F)) : closeCode (code d) = code (closeTree d) := by
  induction d with
  | free q =>
    simp only [code,closeCode,fold_free,ScalarAnnotationData.closeTree,↓reduceIte]
    rw [OrdinalSyntax.ordinalSyntaxHeadClosureCorrect]
  | tracked => simp [code,closeCode,fold_tracked,ScalarAnnotationData.closeTree]
  | add a b iha ihb =>
    simp only [code,closeCode,fold_add] at iha ihb ⊢
    rw [iha,ihb]
    rfl
  | collapse op tail ih =>
    simp only [code,closeCode,fold_collapse] at ih ⊢
    rw [closeOperator_correct,ih]
    rfl

theorem exactClosing : Targets.ExactClosing := by
  exact ⟨fun Γ op => closeOperator_correct op,fun k Γ F d => closeTree_correct d⟩

end LogicLineages.OrdinalComparison.Source.SourceAnnotationCode.Proof
