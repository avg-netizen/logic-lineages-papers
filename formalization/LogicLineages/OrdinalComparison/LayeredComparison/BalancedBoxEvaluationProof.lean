module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationInterfacesProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationTableProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSmallBoxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluation.Proof
open BalancedSyntax BalancedEvaluation BalancedSmallBox

theorem box_valuation_eq (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) (word : List Nat) (hword : word ∈ boxWords k Γ C E F) :
    BaseTermPrograms.valuation (boxTable k Γ C E F word) = boxValuation k Γ C E F word := by
  have hlen := (BalancedSmallBox.Proof.words_spec _ _ _).mp hword |>.1
  funext i
  exact finiteTable_valuation _ _ hlen i

theorem actual_box_results (k : Nat) (Γ : List Nat) (C : Certificate (k :: Γ))
    (E F : Upper k) (word : List Nat) (hword : word ∈ boxWords k Γ C E F) :
    joint (k :: Γ, encodeCertificate (k :: Γ) C, encodeSyntax (k :: Γ) E,
        boxTable k Γ C E F word) =
      (value (k :: Γ) C E (boxValuation k Γ C E F word), rawVariables (k :: Γ) C E) ∧
    joint (k :: Γ, encodeCertificate (k :: Γ) C, encodeSyntax (k :: Γ) F,
        boxTable k Γ C E F word) =
      (value (k :: Γ) C F (boxValuation k Γ C E F word), rawVariables (k :: Γ) C F) ∧
    completeInputs k Γ C E F (BaseTermPrograms.valuation (boxTable k Γ C E F word)) =
      completeInputs k Γ C E F (boxValuation k Γ C E F word) := by
  have hv := box_valuation_eq k Γ C E F word hword
  have he := actualSourceCalibration (k :: Γ) C E (boxTable k Γ C E F word)
  have hf := actualSourceCalibration (k :: Γ) C F (boxTable k Γ C E F word)
  constructor
  · simp only [joint, he.1, he.2, hv]
  constructor
  · simp only [joint, hf.1, hf.2, hv]
  · rw [hv]

theorem exactBoxEvaluation : Targets.ExactBoxEvaluation := by
  refine ⟨finiteTable_computable, ?_, actual_box_results, ?_⟩
  · intro support word hlen
    exact ⟨finiteTable_length support word, finiteTable_valuation support word hlen⟩
  · intro k Γ C E F ν hC hpositive hsmall
    obtain ⟨word, hcanonical, hword, hagree, hpos, houtside, hE, hF, hinputs, hsmall'⟩ :=
      BalancedSmallBox.Proof.exactSmallBranchRepresentative k Γ C E F ν hC hpositive hsmall
    have hv := box_valuation_eq k Γ C E F word hword
    obtain ⟨he, hf, hi⟩ := actual_box_results k Γ C E F word hword
    refine ⟨word, hcanonical, hword, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hv] using hagree
    · simpa only [hv] using houtside
    · exact he.trans (congrArg (fun v => (v, rawVariables (k :: Γ) C E)) hE)
    · exact hf.trans (congrArg (fun v => (v, rawVariables (k :: Γ) C F)) hF)
    · exact hi.trans hinputs
    · simpa only [hv] using hsmall'

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluation.Proof
