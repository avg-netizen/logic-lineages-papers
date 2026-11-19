module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationPartialProof
public import LogicLineages.StandardControlCurrent.PolicyPartialSyntaxProof
public import LogicLineages.OrdinalComparison.SourceAnnotationCodeProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotation

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleSum ScalarAnnotationData SourceAnnotationCode ActiveScalarAnnotation

private theorem freeRaw (p : Policy) {k Γ} {F : Variable Γ (Ty.curriedGround (k+1))}
    (d : Tree k (.ground :: Γ) (.there F)) (hf : ordinalHeadFree (erase d) = true) :
    CurrentGroundAnnotationCode.groundPartialCode p
      (SourceTypedPorts.variableIndex (Γ := .ground :: Γ) (.there F)) (code d) =
      (groundPartial p d).map code := by
  rw [CurrentGroundAnnotationCode.groundPartialCode.eq_def]
  dsimp only
  rw [SourceAnnotationCode.Proof.exactErasure,OrdinalSyntax.ordinalSyntaxHeadFreeCorrect,if_pos hf,
    groundPartial.eq_def,if_pos hf]
  simp only [Option.map_some,code,SourceAnnotationCode.Proof.closeTree_correct]
  rfl

theorem exactPartialCode (p : Policy) (k : Nat) (Γ : List Ty)
    (F : Variable Γ (Ty.curriedGround (k+1))) (d : Tree k (.ground :: Γ) (.there F)) :
    CurrentGroundAnnotationCode.groundPartialCode p
      (SourceTypedPorts.variableIndex (Γ := .ground :: Γ) (.there F)) (code d) =
      (groundPartial p d).map code := by
  induction d with
  | free q =>
    by_cases hf : ordinalHeadFree (erase (Tree.free (k := k) (F := .there F) q)) = true
    · exact freeRaw p _ hf
    rw [CurrentGroundAnnotationCode.groundPartialCode.eq_def]
    dsimp only
    rw [SourceAnnotationCode.Proof.exactErasure,OrdinalSyntax.ordinalSyntaxHeadFreeCorrect,if_neg hf,
      groundPartial.eq_def,if_neg hf]
    have hm : code (Tree.free (k := k) (F := .there F) q) % 4 = 0 := by simp [code]
    have hd : code (Tree.free (k := k) (F := .there F) q) / 4 = OrdinalSyntax.typedCode q := by simp [code]
    rw [dif_pos hm,hd]
    have hp := PolicyPartialSyntaxProof.literal p Γ .ground 0 q
    change PolicyPartial.run p 0 0 (OrdinalSyntax.typedCode q) = _ at hp
    rw [hp]
    cases hv : AdmissiblePartial.run p 0 q with
    | none => simp [hv]
    | some v => simp [hv,code,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  | tracked => exact freeRaw p _ rfl
  | add a b iha ihb =>
    by_cases hf : ordinalHeadFree (erase (.add a b)) = true
    · exact freeRaw p _ hf
    rw [CurrentGroundAnnotationCode.groundPartialCode.eq_def]
    dsimp only
    rw [SourceAnnotationCode.Proof.exactErasure,OrdinalSyntax.ordinalSyntaxHeadFreeCorrect,if_neg hf,
      groundPartial.eq_def,if_neg hf]
    have hm : code (.add a b) % 4 = 2 := by simp [code]
    have hd : code (.add a b) / 4 = Nat.pair (code a) (code b) := by simp only [code]; omega
    simp only [hm,hd,Nat.unpair_pair,show ¬(2:Nat)=0 by decide,
      show ¬(2:Nat)=1 by decide,↓reduceIte,↓reduceDIte]
    rw [iha,ihb]
    cases ha : groundPartial p a with
    | none => simp [ha]
    | some a' =>
      cases hb : groundPartial p b with
      | none => simp [ha,hb]
      | some b' => simpa [ha,hb,Option.bind_some,bind,pure] using markerThree p a' b'
  | collapse op tail ih =>
    by_cases hf : ordinalHeadFree (erase (.collapse op tail)) = true
    · exact freeRaw p _ hf
    rw [CurrentGroundAnnotationCode.groundPartialCode.eq_def]
    dsimp only
    rw [SourceAnnotationCode.Proof.exactErasure,OrdinalSyntax.ordinalSyntaxHeadFreeCorrect,if_neg hf,
      groundPartial.eq_def,if_neg hf]
    have hm : code (.collapse op tail) % 4 = 3 := by simp [code]
    have hd : code (.collapse op tail) / 4 = Nat.pair (operatorCode op) (code tail) := by simp only [code]; omega
    simp only [hm,hd,Nat.unpair_pair,show ¬(3:Nat)=0 by decide,
      show ¬(3:Nat)=1 by decide,show ¬(3:Nat)=2 by decide,↓reduceIte,↓reduceDIte]
    rw [ih,SourceAnnotationCode.Proof.closeOperator_correct]
    cases ht : groundPartial p tail <;> simp [ht,code]

theorem actualGroundPartial : CurrentGroundAnnotationTargets.ActualGroundPartial := by
  intro p k Γ F d hd
  obtain ⟨v,e,hv,he,her,hValid⟩ := typedGroundPartial p d hd
  refine ⟨v,e,hv,he,her,hValid,?_,?_⟩
  · rw [her]
    exact CurrentGroundBudget.groundPartialActivity p F _ v hv
  · rw [exactPartialCode p k Γ F d,he,Option.map_some]

end LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotation
