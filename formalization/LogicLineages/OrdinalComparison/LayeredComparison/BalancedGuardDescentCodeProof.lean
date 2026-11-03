module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescentTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapterSemanticProof
public import Mathlib.Data.List.GetD
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescent.Proof
open BalancedSyntax BalancedEvaluation CommonHeadCompiler

theorem numeral_code (Γ : List Nat) (c : Nat) :
    BalancedAffineCode.numeral Γ c = encodeSyntax Γ (Affine.numeral Γ c) :=
  (BalancedAffineCode.Proof.exactLiteralOperations Γ).1 c

theorem label_code (Γ : List Nat) (labels : List (Syntax Γ)) (i : Nat) :
    labelCode Γ (labels.map (encodeSyntax Γ)) i = encodeSyntax Γ (label Γ labels i) := by
  unfold labelCode label
  rw [numeral_code]
  exact List.getD_map labels (Affine.numeral Γ 0) (encodeSyntax Γ)

theorem child_code (Γ : List Nat) (C : Certificate Γ)
    (labels : List (Syntax Γ)) (q : Instruction) :
    child Γ (encodeCertificate Γ C) (labels.map (encodeSyntax Γ)) q =
      encodeCall Γ C (typedChild Γ labels q) := by
  unfold child typedChild
  split_ifs <;> simp only [encodeCall, label_code, numeral_code]

theorem child_shape (Γ : List Nat) (C : Nat) (labels : List Nat) (q : Instruction) :
    (child Γ C labels q).1 = Γ := by
  unfold child
  split_ifs <;> rfl

private theorem negative_encode (p : BaseFormula.Formula) :
    (BaseFormula.Formula.negative p).encode = p.encode ++ [(5,0,0)] := rfl
private theorem conjunction_encode (p q : BaseFormula.Formula) :
    (BaseFormula.Formula.conjunction p q).encode = p.encode ++ q.encode ++ [(6,0,0)] := rfl
private theorem disjunction_encode (p q : BaseFormula.Formula) :
    (BaseFormula.Formula.disjunction p q).encode = p.encode ++ q.encode ++ [(7,0,0)] := rfl

theorem translate_encode (Γ : List Nat) (lower : Lower Γ) (labels : List (Syntax Γ))
    (p : CommonHeadLargeGuards.Formula) :
    (translateGuard Γ lower labels p).encode = (CommonHeadCompiler.encode p).flatMap
      (fun q => let a := typedChild Γ labels q
        instructionCode q (lower a.1 a.2.1 a.2.2).encode) := by
  induction p with
  | truth => simp [translateGuard, BaseFormula.Formula.encode, BaseFormula.Formula.guardView,
      CommonHeadCompiler.encode, instructionCode]
  | falsity => simp [translateGuard, BaseFormula.Formula.encode, BaseFormula.Formula.guardView,
      CommonHeadCompiler.encode, instructionCode]
  | eq i j => simp [translateGuard, CommonHeadCompiler.encode, instructionCode, typedChild]
  | lt i j => simp [translateGuard, CommonHeadCompiler.encode, instructionCode, typedChild]
  | bound c i => simp [translateGuard, BaseFormula.Formula.encode, BaseFormula.Formula.guardView,
      CommonHeadCompiler.encode, instructionCode, typedChild]
  | neg p ih =>
    rw [translateGuard, negative_encode, ih]
    simp only [CommonHeadCompiler.encode, List.flatMap_append, List.flatMap_cons, List.flatMap_nil]
    rfl
  | conj p q ihp ihq =>
    rw [translateGuard, conjunction_encode, ihp, ihq]
    simp only [CommonHeadCompiler.encode, List.flatMap_append, List.flatMap_cons, List.flatMap_nil]
    rfl
  | disj p q ihp ihq =>
    rw [translateGuard, disjunction_encode, ihp, ihq]
    simp only [CommonHeadCompiler.encode, List.flatMap_append, List.flatMap_cons, List.flatMap_nil]
    rfl

private theorem zip_assembly {α β γ : Type} (xs : List α) (f : α → β) (g : α → β → List γ) :
    (xs.zipWith g (xs.map f)).flatten = xs.flatMap (fun x => g x (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.zipWith_cons_cons, List.flatten_cons, List.flatMap_cons, ih]

theorem exactPostfixSubstitution : Targets.ExactPostfixSubstitution := by
  refine ⟨child_code, ?_, ?_⟩
  · intro Γ lower labels code
    exact List.length_map _
  · intro Γ lower labels p
    unfold assemble typedResults
    rw [zip_assembly]
    exact (translate_encode Γ lower labels p).symm

theorem exactActualCallsAndDescent : Targets.ExactActualCallsAndDescent := by
  constructor
  · intro k Γ C E F desired
    constructor
    · simp only [sourceChildren, children, List.length_map]
    · intro a ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      simp only [measure, child_shape, List.length_cons]
      omega
  · intro k Γ C E F desired lower
    obtain ⟨hc, ht⟩ := BalancedSourceAdapter.Proof.exactLiteralSourceLabels k Γ C E F
    have hp := (BalancedSourceAdapter.Proof.exactAssembledSourceCode k Γ C E F desired).1
    constructor
    · unfold sourceChildren children
      rw [hc, ht, hp]
      apply List.map_congr_left
      intro q hq
      exact child_code Γ C.1 _ q
    · unfold sourceAssemble
      rw [hp]
      exact exactPostfixSubstitution.2.2 Γ lower _ _

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescent.Proof
