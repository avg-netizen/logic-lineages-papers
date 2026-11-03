module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparisonValueProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseFormulaProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparison.Proof
open CommonLayerSyntax

private theorem translated_truth (Γ:List Nat) (lower:Nat→Nat→Int→BaseFormula.Formula)
    (ν:Nat→Nat)
    (hl:∀E F desired,(lower E F desired).eval ν↔
      Int.sign ((codedValue Γ E ν:Int)-(codedValue Γ F ν:Int))=desired)
    (N:Nat) (args:List Nat) (p:CommonHeadLargeGuards.Formula):
    (translateGuard lower Γ.length N args p).eval ν↔
      p.eval (fun i=>N+codedValue Γ (args.getD i (constantCode Γ.length 0)) ν):=by
  induction p with
  | truth=>rfl
  | falsity=>rfl
  | eq i j=>
    change (lower _ _ 0).eval ν↔N+_ =N+_
    rw [hl,sign_zero]
    omega
  | lt i j=>
    change (lower _ _ (-1)).eval ν↔N+_ <N+_
    rw [hl,sign_negative]
    omega
  | bound c i=>
    by_cases hc:c≤N
    · simp only [translateGuard,if_pos hc,BaseFormula.Formula.eval,CommonHeadLargeGuards.Formula.eval]
      exact iff_of_true trivial (hc.trans (Nat.le_add_right _ _))
    · simp only [translateGuard,if_neg hc,BaseFormula.Formula.eval,CommonHeadLargeGuards.Formula.eval]
      rw [hl,sign_negative,constant_value]
      omega
  | neg p ih=>exact not_congr ih
  | conj p q ihp ihq=>exact and_congr ihp ihq
  | disj p q ihp ihq=>exact or_congr ihp ihq

theorem codedComparison:Targets.ExactCodedComparison:=by
  intro Γ
  induction Γ with
  | nil=>
    intro hg E F desired ν
    exact base_exact E F desired ν
  | cons rho Γ ih=>
    intro hg E F desired ν
    have hr:Order.IsSuccLimit rho.1.repr:=hg rho (by simp)
    have ht:genuineHeads Γ:=by
      intro r hm
      exact hg r (by simp [hm])
    change (translateGuard (compile (headCodes Γ)) (headCodes Γ).length
      (rawNormCode (rawNoteEncode rho.1)) (rowArguments E F)
      (CommonHeadCompiler.compile (rawNoteEncode rho.1) (rowConstant E F) (rowCoefficients E F) desired)).eval ν↔_
    rw [translated_truth (headCodes Γ) _ ν (fun A B d=>ih ht A B d ν)]
    rw [CommonHeadCompiler.Proof.exactSourceRow rho hr]
    · rw [row_difference]
      simp only [headCodes,List.map_cons]
    · intro i hi
      have hn:rawNormCode (rawNoteEncode rho.1)=actualOrdinalNorm rho.1.repr:=by
        rw [rawNormCodeCorrect,actualOrdinalNorm_notationCorrespondence rho]
      rw [hn]
      omega

theorem actualComparison:Targets.ActualSourceComparison:=by
  intro Γ hg E F desired ν
  unfold compileCode
  rw [(BaseFormula.Proof.literalBaseFormulaCode _).1 ν]
  rw [codedComparison Γ hg]
  rw [CommonLayerSyntax.Proof.sourceCalibration Γ E ν,
    CommonLayerSyntax.Proof.sourceCalibration Γ F ν]
end LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparison.Proof
