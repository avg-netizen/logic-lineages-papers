module
public import LogicLineages.StandardControlCurrent.PolicyPartialMergeProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyPartialSyntaxProof
open OrdinalComparison Source Source.OrdinalSyntax
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
private theorem range_map (n : Nat) (f : Nat → Nat) :
    (List.range n).map f = List.ofFn (fun j : Fin n => f j.val) := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp

private theorem list_lookup {n : Nat} (f : Fin n → Nat) (j : Fin n) :
    (List.ofFn f).getD j.val 0 = f j := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt]

private theorem free_codes {Γ : List Ty} {σ : Ty} (i : Nat)
    (t : OrdinalExpression (σ::Γ)) :
    partialFree σ.level i (typedCode t) =
      List.ofFn (fun j => typedCode (ordinalFreePartialVector i t j)) := by
  rw [partialFree, range_map, ordinalSyntaxHeadClosureCorrect Γ σ t]
  congr 1
  funext j
  simp only [ordinalFreePartialVector]
  split <;> simp_all [typedCode, code, node, ordinalSyntaxHeadClosureCorrect Γ σ t]

private theorem free_run (p : AdmissibleSum.Policy) {Γ : List Ty} {σ : Ty} (i : Nat)
    (t : OrdinalExpression (σ::Γ)) (hf : ordinalHeadFree t = true) :
    PolicyPartial.run p σ.level i (typedCode t) =
      (AdmissiblePartial.run p i t).map (fun v => List.ofFn (fun j => typedCode (v j))) := by
  rw [PolicyPartial.run p, ordinalSyntaxHeadFreeCorrect Γ σ t, hf, AdmissiblePartial.run.eq_def, hf]
  simpa using congrArg some (free_codes i t)

private theorem collapse_codes {Γ : List Ty} {σ : Ty} (h : OrdinalExpression (σ::Γ))
    (a b : OrdinalPartialVector Γ σ) :
    partialCollapse σ.level (typedCode h) (List.ofFn (fun j => typedCode (a j)))
      (List.ofFn (fun j => typedCode (b j))) =
    List.ofFn (fun j => typedCode (if j.val=0 then .collapse (ordinalHeadClosure h) (b 0)
      else .add (a j) (b j))) := by
  rw [partialCollapse, range_map, ordinalSyntaxHeadClosureCorrect Γ σ h]
  congr 1
  funext j
  simp only [list_lookup]
  by_cases hj : j.val=0
  · simp [hj, node, typedCode, code, ordinalSyntaxHeadClosureCorrect Γ σ h,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  · simp [hj, node, typedCode, code]
theorem literal : PolicyPartialTargets.LiteralCalibration := by
  intro p Γ σ i t
  induction t generalizing i with
  | zero => exact free_run p i .zero rfl
  | one => exact free_run p i .one rfl
  | omega => exact free_run p i .omega rfl
  | var c =>
    rcases c with ⟨τ, v, k⟩
    cases v with
    | there v => exact free_run p i (.var ⟨_, .there v, k⟩) rfl
    | here =>
      have hm : (typedCode (.var ⟨σ, Variable.here, k⟩ : OrdinalExpression (σ::Γ)))%8=3 := by
        dsimp [typedCode, code]; omega
      have hd : (typedCode (.var ⟨σ, Variable.here, k⟩ : OrdinalExpression (σ::Γ)))/8=Nat.pair 0 k.val := by
        dsimp [typedCode, code, componentCode, SourceTypedPorts.variableIndex]; omega
      rw [PolicyPartial.run p, ordinalSyntaxHeadFreeCorrect Γ σ _, AdmissiblePartial.run.eq_def]
      simp [ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs, hm, hd]
      by_cases hi : i=k.val <;> simp [hi, typedCode, code, List.replicate_succ]
  | add a b iha ihb =>
    by_cases hf : ordinalHeadFree (.add a b)=true
    · exact free_run p i (.add a b) hf
    have hm : (typedCode (.add a b))%8=4 := by dsimp [typedCode, code]; omega
    have hd : (typedCode (.add a b))/8=Nat.pair (typedCode a) (typedCode b) := by dsimp [typedCode, code]; omega
    rw [PolicyPartial.run p, ordinalSyntaxHeadFreeCorrect Γ σ _, AdmissiblePartial.run.eq_def]
    simp only [Bool.eq_false_iff.mpr hf, Bool.false_eq_true, if_false, hm, hd, Nat.unpair_pair]
    simp only [show ¬(4:Nat)=3 by decide, show (4:Nat)=4 by rfl, if_false, if_true,
      true_or, dite_true]
    rw [iha i, ihb i]
    cases hpa : AdmissiblePartial.run p i a with
    | none => simp
    | some pa =>
      cases hpb : AdmissiblePartial.run p i b with
      | none => simp
      | some pb => simpa [bind,pure] using PolicyPartialMergeProof.merge_codes p 4 pa pb
  | emul a b iha ihb =>
    by_cases hf : ordinalHeadFree (.emul a b)=true
    · exact free_run p i (.emul a b) hf
    have hm : (typedCode (.emul a b))%8=5 := by dsimp [typedCode, code]; omega
    have hd : (typedCode (.emul a b))/8=Nat.pair (typedCode a) (typedCode b) := by dsimp [typedCode, code]; omega
    rw [PolicyPartial.run p, ordinalSyntaxHeadFreeCorrect Γ σ _, AdmissiblePartial.run.eq_def]
    simp only [Bool.eq_false_iff.mpr hf, Bool.false_eq_true, if_false, hm, hd, Nat.unpair_pair]
    simp only [show ¬(5:Nat)=3 by decide, show ¬(5:Nat)=4 by decide, show (5:Nat)=5 by rfl,
      if_false, if_true, false_or, true_or, dite_true]
    by_cases hi : 0 < i
    · simp only [if_pos hi]
      rw [iha (i+1), ihb i]
      cases hpa : AdmissiblePartial.run p (i+1) a with
      | none => simp
      | some pa =>
        cases hpb : AdmissiblePartial.run p i b with
        | none => simp
        | some pb => simpa [bind,pure] using PolicyPartialMergeProof.merge_codes p 5 pa pb
    · simp [hi]
  | collapse a b iha ihb =>
    by_cases hf : ordinalHeadFree (.collapse a b)=true
    · exact free_run p i (.collapse a b) hf
    have hm : (typedCode (.collapse a b))%8=6 := by dsimp [typedCode, code]; omega
    have hd : (typedCode (.collapse a b))/8=Nat.pair (typedCode a) (typedCode b) := by dsimp [typedCode, code]; omega
    rw [PolicyPartial.run p, ordinalSyntaxHeadFreeCorrect Γ σ _, AdmissiblePartial.run.eq_def]
    simp only [Bool.eq_false_iff.mpr hf, Bool.false_eq_true, if_false, hm, hd, Nat.unpair_pair]
    simp only [show ¬(6:Nat)=3 by decide, show ¬(6:Nat)=4 by decide, show ¬(6:Nat)=5 by decide,
      show (6:Nat)=6 by rfl, if_false, if_true, false_or, dite_true]
    by_cases hi : i=0
    · simp only [if_pos hi]
      rw [iha 1, ihb 0]
      cases hpa : AdmissiblePartial.run p 1 a with
      | none => simp
      | some pa =>
        cases hpb : AdmissiblePartial.run p 0 b with
        | none => simp
        | some pb => simpa using congrArg some (collapse_codes a pa pb)
    · simp [hi]
end LogicLineages.StandardControlCurrent.PolicyPartialSyntaxProof
