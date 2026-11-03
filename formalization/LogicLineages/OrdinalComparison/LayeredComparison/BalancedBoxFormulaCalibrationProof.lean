module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormulaLiteralProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapterSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormula.Proof
open BalancedSyntax BalancedEvaluation BalancedSmallBox

theorem source_sign_actual (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) (word : List Nat) (hw : word ∈ boxWords k Γ C E F) :
    sourceSign k Γ C E F word =
      Int.sign ((value (k :: Γ) C E (boxValuation k Γ C E F word) : Int) -
        (value (k :: Γ) C F (boxValuation k Γ C E F word) : Int)) := by
  obtain ⟨he, hf, _⟩ := BalancedBoxEvaluation.Proof.actual_box_results k Γ C E F word hw
  change Int.sign (((joint (k :: Γ, encodeCertificate (k :: Γ) C,
      encodeSyntax (k :: Γ) E, BalancedBoxEvaluation.boxTable k Γ C E F word)).1 : Int) -
    ((joint (k :: Γ, encodeCertificate (k :: Γ) C,
      encodeSyntax (k :: Γ) F, BalancedBoxEvaluation.boxTable k Γ C E F word)).1 : Int)) = _
  rw [he, hf]

theorem actualSourceCodeCalibration : Targets.ActualSourceCodeCalibration := by
  intro k Γ C E F desired
  let c := encodeCertificate (k :: Γ) C
  let e := encodeSyntax (k :: Γ) E
  let f := encodeSyntax (k :: Γ) F
  have he := BalancedBoxEvaluation.Proof.actualSourceCalibration (k :: Γ) C E []
  have hf := BalancedBoxEvaluation.Proof.actualSourceCalibration (k :: Γ) C F []
  have hs : rawSupport k Γ c e f = sourceSupport k Γ C E F := by
    simp only [rawSupport, c, e, f, he.2, hf.2, sourceSupport, sourceAmbient]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ht⟩ :=
    BalancedSourceAdapter.Proof.exactOriginalMetadata k Γ E F
  have hw : rawWords k Γ c e f = boxWords k Γ C E F := by
    unfold rawWords boxWords
    rw [hs]
    exact congrArg (fun L => singleCoreBoxWords L (sourceSupport k Γ C E F).length) ht
  refine ⟨hs, ht, hw, ?_, ?_⟩
  · intro word hword
    rw [hs]
    exact source_sign_actual k Γ C E F word hword
  · unfold formulaCode
    rw [hs, hw]
    change CommonHeadCode.disjoin (((boxWords k Γ C E F).filter
      (fun word => decide (sourceSign k Γ C E F word = desired))).map
        (pointCode (sourceSupport k Γ C E F))) = _
    unfold sourceFormula
    rw [← disjunction_code]
    simp only [List.map_map, Function.comp_def]
    apply congrArg CommonHeadCode.disjoin
    apply List.map_congr_left
    intro word hword
    exact point_code _ _

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormula.Proof
