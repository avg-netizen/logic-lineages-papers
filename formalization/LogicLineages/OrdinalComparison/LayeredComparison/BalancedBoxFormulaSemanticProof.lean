module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormulaLiteralProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormula.Proof
open BalancedSyntax BalancedSmallBox

private theorem source_formula_eval (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E F : Upper k) (desired : Int) (ν : Nat → Nat) :
    (sourceFormula k Γ C E F desired).eval ν ↔
      ∃ word ∈ boxWords k Γ C E F,
        sourceSign k Γ C E F word = desired ∧
        (pointFormula (sourceSupport k Γ C E F) word).eval ν := by
  unfold sourceFormula
  rw [disjunction_eval]
  constructor
  · rintro ⟨p, hp, htrue⟩
    obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hp
    have hw := List.mem_filter.mp hword
    exact ⟨word, hw.1, of_decide_eq_true hw.2, htrue⟩
  · rintro ⟨word, hword, hsign, htrue⟩
    refine ⟨pointFormula (sourceSupport k Γ C E F) word, ?_, htrue⟩
    apply List.mem_map.mpr
    refine ⟨word, ?_, rfl⟩
    exact List.mem_filter.mpr ⟨hword, by simpa only [decide_eq_true_eq] using hsign⟩

/-- Both values are obtained from the accepted evaluator at the same original
raw table. No genuine-certificate or positive-valuation premise is used. -/
private theorem source_sign_value (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E F : Upper k) (word : List Nat)
    (hword : word ∈ boxWords k Γ C E F) :
    sourceSign k Γ C E F word =
      Int.sign ((value (k :: Γ) C E (boxValuation k Γ C E F word) : Int) -
        (value (k :: Γ) C F (boxValuation k Γ C E F word) : Int)) := by
  obtain ⟨hE, hF, hinputs⟩ :=
    BalancedBoxEvaluation.Proof.actual_box_results k Γ C E F word hword
  change Int.sign
    (((BalancedEvaluation.joint (k :: Γ,
      BalancedEvaluation.encodeCertificate (k :: Γ) C,
      BalancedEvaluation.encodeSyntax (k :: Γ) E,
      BalancedBoxEvaluation.boxTable k Γ C E F word)).1 : Int) -
    ((BalancedEvaluation.joint (k :: Γ,
      BalancedEvaluation.encodeCertificate (k :: Γ) C,
      BalancedEvaluation.encodeSyntax (k :: Γ) F,
      BalancedBoxEvaluation.boxTable k Γ C E F word)).1 : Int)) = _
  rw [hE, hF]

/-- The representative's outside-one convention is removed by actual source
support stability, leaving every outside coordinate of ν unrestricted. -/
private theorem canonical_sign (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E F : Upper k) (ν : Nat → Nat)
    (hword : (sourceSupport k Γ C E F).map ν ∈ boxWords k Γ C E F) :
    sourceSign k Γ C E F ((sourceSupport k Γ C E F).map ν) =
      Int.sign ((value (k :: Γ) C E ν : Int) - (value (k :: Γ) C F ν : Int)) := by
  have hagree : ∀ i ∈ sourceAmbient k Γ C E F,
      boxValuation k Γ C E F ((sourceSupport k Γ C E F).map ν) i = ν i := by
    intro i hi
    apply BalancedSmallBox.Proof.lookup_map
    simpa only [sourceSupport, List.mem_dedup] using hi
  have hstable := BalancedSmallBox.Proof.actualSourceSupportStability k Γ C E F
    (boxValuation k Γ C E F ((sourceSupport k Γ C E F).map ν)) ν hagree
  rw [source_sign_value k Γ C E F _ hword, hstable.1, hstable.2.1]

/-- Exact truth on the original positive box for all typed source data and all
raw valuations. In particular, this is not conditional on a genuine certificate. -/
theorem finite_box_truth (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E F : Upper k) (desired : Int) (ν : Nat → Nat) :
    (sourceFormula k Γ C E F desired).eval ν ↔
      (∀ i ∈ sourceAmbient k Γ C E F, 0 < ν i ∧ ν i < originalThreshold E F) ∧
      Int.sign ((value (k :: Γ) C E ν : Int) - (value (k :: Γ) C F ν : Int)) = desired := by
  constructor
  · intro hformula
    obtain ⟨word, hword, hsign, hpoint⟩ :=
      (source_formula_eval k Γ C E F desired ν).mp hformula
    have hlen := (BalancedSmallBox.Proof.words_spec _ _ _).mp hword |>.1
    have hcanonical := (point_eval_iff_map (sourceSupport k Γ C E F) word ν hlen).mp hpoint
    subst word
    have hspec := (BalancedSmallBox.Proof.words_spec _ _ _).mp hword
    refine ⟨?_, ?_⟩
    · intro i hi
      have hs : i ∈ sourceSupport k Γ C E F := by
        simpa only [sourceSupport, List.mem_dedup] using hi
      exact hspec.2 (ν i) (List.mem_map.mpr ⟨i, hs, rfl⟩)
    · rw [← canonical_sign k Γ C E F ν hword]
      exact hsign
  · rintro ⟨hbound, hsign⟩
    have hword : (sourceSupport k Γ C E F).map ν ∈ boxWords k Γ C E F := by
      apply (BalancedSmallBox.Proof.words_spec _ _ _).mpr
      refine ⟨List.length_map ν, ?_⟩
      intro v hv
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
      apply hbound i
      simpa only [sourceSupport, List.mem_dedup] using hi
    apply (source_formula_eval k Γ C E F desired ν).mpr
    refine ⟨(sourceSupport k Γ C E F).map ν, hword, ?_, ?_⟩
    · exact (canonical_sign k Γ C E F ν hword).trans hsign
    · exact (point_eval_iff_map _ _ ν (List.length_map ν)).mpr rfl

theorem exactFiniteBoxFormula : Targets.ExactFiniteBoxFormula := by
  refine ⟨finite_box_truth, ?_⟩
  intro k Γ C E F desired ν hC hpositive hsmall
  have hbounds := BalancedSmallBox.Proof.actualSmallInputBounds k Γ C E F ν hC hsmall
  have hexact := finite_box_truth k Γ C E F desired ν
  constructor
  · intro hformula
    exact (hexact.mp hformula).2
  · intro hsign
    apply hexact.mpr
    exact ⟨fun i hi => ⟨hpositive i hi, hbounds.2.2.2 i hi⟩, hsign⟩

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxFormula.Proof
