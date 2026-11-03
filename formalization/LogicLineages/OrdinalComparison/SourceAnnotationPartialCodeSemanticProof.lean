module
public import LogicLineages.OrdinalComparison.SourceAnnotationPartialCodeTargets
public import LogicLineages.OrdinalComparison.SourceAnnotationCodeProof
public import LogicLineages.OrdinalComparison.ScalarAnnotationDataProof
public import LogicLineages.OrdinalComparison.WWDefaultSyntaxAbstractionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAnnotationPartialCode.Proof
open ScalarAnnotationData SourceAnnotationCode

private theorem free_correct {k Γ} {F : Variable Γ (Ty.curriedGround (k+1))}
    (d : Tree k (.ground :: Γ) (.there F)) (hf : ordinalHeadFree (erase d) = true) :
    groundPartialCode (SourceTypedPorts.variableIndex (Γ := .ground :: Γ) (.there F)) (code d) =
      (groundPartial d).map code := by
  rw [groundPartialCode.eq_def]
  dsimp only
  rw [SourceAnnotationCode.Proof.exactErasure,
    OrdinalSyntax.ordinalSyntaxHeadFreeCorrect,if_pos hf,
    groundPartial.eq_def,if_pos hf]
  simp only [Option.map_some,code,SourceAnnotationCode.Proof.closeTree_correct]
  rfl

theorem exactPartialCode : Targets.ExactPartialCode := by
  intro k Γ F d
  induction d with
  | free q =>
    by_cases hf : ordinalHeadFree (erase (Tree.free (k := k) (F := .there F) q)) = true
    · exact free_correct _ hf
    rw [groundPartialCode.eq_def]
    dsimp only
    rw [SourceAnnotationCode.Proof.exactErasure,
      OrdinalSyntax.ordinalSyntaxHeadFreeCorrect,if_neg hf,
      groundPartial.eq_def,if_neg hf]
    have hm : code (Tree.free (k := k) (F := .there F) q) % 4 = 0 := by simp [code]
    have hd : code (Tree.free (k := k) (F := .there F) q) / 4 = OrdinalSyntax.typedCode q := by simp [code]
    rw [dif_pos hm,hd]
    have hp := OrdinalSyntax.defaultSyntaxPartialCorrect Γ .ground 0 q
    change OrdinalSyntax.partialRun 0 0 (OrdinalSyntax.typedCode q) = _ at hp
    rw [hp]
    cases hv : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 q with
    | none => simp [hv]
    | some v =>
      simp [hv,code,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  | tracked => exact free_correct _ rfl
  | add a b iha ihb =>
    by_cases hf : ordinalHeadFree (erase (.add a b)) = true
    · exact free_correct _ hf
    rw [groundPartialCode.eq_def]
    dsimp only
    rw [SourceAnnotationCode.Proof.exactErasure,
      OrdinalSyntax.ordinalSyntaxHeadFreeCorrect,if_neg hf,
      groundPartial.eq_def,if_neg hf]
    have hm : code (.add a b) % 4 = 2 := by simp [code]
    have hd : code (.add a b) / 4 = Nat.pair (code a) (code b) := by simp only [code]; omega
    simp only [hm,hd,Nat.unpair_pair,show ¬(2:Nat)=0 by decide,
      show ¬(2:Nat)=1 by decide,↓reduceIte,↓reduceDIte]
    rw [iha,ihb]
    cases ha : groundPartial a <;> cases hb : groundPartial b <;> simp [code,OrdinalSyntax.typedCode,OrdinalSyntax.code]
  | collapse op tail ih =>
    by_cases hf : ordinalHeadFree (erase (.collapse op tail)) = true
    · exact free_correct _ hf
    rw [groundPartialCode.eq_def]
    dsimp only
    rw [SourceAnnotationCode.Proof.exactErasure,
      OrdinalSyntax.ordinalSyntaxHeadFreeCorrect,if_neg hf,
      groundPartial.eq_def,if_neg hf]
    have hm : code (.collapse op tail) % 4 = 3 := by simp [code]
    have hd : code (.collapse op tail) / 4 = Nat.pair (operatorCode op) (code tail) := by simp only [code]; omega
    simp only [hm,hd,Nat.unpair_pair,show ¬(3:Nat)=0 by decide,
      show ¬(3:Nat)=1 by decide,show ¬(3:Nat)=2 by decide,↓reduceIte,↓reduceDIte]
    rw [ih,SourceAnnotationCode.Proof.closeOperator_correct]
    cases ht : groundPartial tail <;> simp [code]

theorem validActualPartial : Targets.ValidActualPartial := by
  intro k Γ F d hd
  obtain ⟨out,v,hout,hv,he,hvalid⟩ := ScalarAnnotationData.Proof.exactGroundPartial k Γ F d hd
  refine ⟨out,v,?_,hout,hv,?_,hvalid⟩
  · rw [exactPartialCode,hout,Option.map_some]
  · rw [SourceAnnotationCode.Proof.exactErasure,he]
end LogicLineages.OrdinalComparison.Source.SourceAnnotationPartialCode.Proof
