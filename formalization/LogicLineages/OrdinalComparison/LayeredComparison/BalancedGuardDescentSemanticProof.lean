module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescentTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineSyntaxClosureProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsLabelsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsSourceProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescent.Proof
open BalancedSyntax
open BalancedSyntax.Affine.Proof

/-- The actual lower-source zero is genuine even outside the label range. -/
private theorem label_genuine (Γ : List Nat) (labels : List (Syntax Γ))
    (hg : ∀ T ∈ labels, genuineExpression Γ T) (j : Nat) :
    genuineExpression Γ (label Γ labels j) := by
  by_cases hj : j < labels.length
  · rw [label, List.getD_eq_getElem _ _ hj]
    exact hg _ (List.getElem_mem hj)
  · rw [label, List.getD_eq_default _ _ (by omega)]
    exact genuine_numeral Γ 0

/-- Defaults contribute no variables, so every selected label stays inside
its supplied list's actual support under the same certificate. -/
private theorem label_support (Γ : List Nat) (C : Certificate Γ)
    (labels : List (Syntax Γ)) (j i : Nat)
    (hi : i ∈ rawVariables Γ C (label Γ labels j)) :
    i ∈ labelSupport Γ C labels := by
  by_cases hj : j < labels.length
  · rw [label, List.getD_eq_getElem _ _ hj] at hi
    exact List.mem_flatMap.mpr ⟨_, List.getElem_mem hj, hi⟩
  · rw [label, List.getD_eq_default _ _ (by omega), rawVariables_numeral] at hi
    cases hi

private theorem label_pair_positive (Γ : List Nat) (C : Certificate Γ)
    (labels : List (Syntax Γ)) (ν : Nat → Nat)
    (hpos : ∀ i ∈ labelSupport Γ C labels, 0 < ν i) (j k : Nat) :
    ∀ i ∈ rawVariables Γ C (label Γ labels j) ++
      rawVariables Γ C (label Γ labels k), 0 < ν i := by
  intro i hi
  rcases List.mem_append.mp hi with hj | hk
  · exact hpos i (label_support Γ C labels j i hj)
  · exact hpos i (label_support Γ C labels k i hk)

private theorem label_numeral_positive (Γ : List Nat) (C : Certificate Γ)
    (labels : List (Syntax Γ)) (ν : Nat → Nat)
    (hpos : ∀ i ∈ labelSupport Γ C labels, 0 < ν i) (j c : Nat) :
    ∀ i ∈ rawVariables Γ C (label Γ labels j) ++
      rawVariables Γ C (Affine.numeral Γ c), 0 < ν i := by
  intro i hi
  rw [rawVariables_numeral, List.append_nil] at hi
  exact hpos i (label_support Γ C labels j i hi)

/-- Every atomic call is an instance of lower correctness on its own actual
pair support. Bounds retain their literal negation, including at zero. -/
private theorem translate_eval (Γ : List Nat) (C : Certificate Γ)
    (lower : Lower Γ) (labels : List (Syntax Γ)) (ν : Nat → Nat)
    (hc : LowerCorrect Γ C lower ν)
    (hg : ∀ T ∈ labels, genuineExpression Γ T)
    (hpos : ∀ i ∈ labelSupport Γ C labels, 0 < ν i)
    (p : CommonHeadLargeGuards.Formula) :
    (translateGuard Γ lower labels p).eval ν ↔
      p.eval (labelValuation Γ C labels ν) := by
  induction p with
  | truth => rfl
  | falsity => rfl
  | eq i j =>
    change (lower (label Γ labels i) (label Γ labels j) 0).eval ν ↔
      value Γ C (label Γ labels i) ν = value Γ C (label Γ labels j) ν
    rw [hc _ _ 0 (label_genuine Γ labels hg i) (label_genuine Γ labels hg j)
      (label_pair_positive Γ C labels ν hpos i j), Int.sign_eq_zero_iff_zero]
    omega
  | lt i j =>
    change (lower (label Γ labels i) (label Γ labels j) (-1)).eval ν ↔
      value Γ C (label Γ labels i) ν < value Γ C (label Γ labels j) ν
    rw [hc _ _ (-1) (label_genuine Γ labels hg i) (label_genuine Γ labels hg j)
      (label_pair_positive Γ C labels ν hpos i j), Int.sign_eq_neg_one_iff_neg]
    omega
  | bound c i =>
    change (¬(lower (label Γ labels i) (Affine.numeral Γ c) (-1)).eval ν) ↔
      c ≤ value Γ C (label Γ labels i) ν
    rw [hc _ _ (-1) (label_genuine Γ labels hg i) (genuine_numeral Γ c)
      (label_numeral_positive Γ C labels ν hpos i c),
      Int.sign_eq_neg_one_iff_neg, value_numeral]
    omega
  | neg p ih => exact not_congr ih
  | conj p q ihp ihq => exact and_congr ihp ihq
  | disj p q ihp ihq => exact or_congr ihp ihq

/-- Syntactic support uses only the separate structural premise. It requires
neither genuine labels nor a positive valuation. -/
private theorem translate_support (Γ : List Nat) (C : Certificate Γ)
    (lower : Lower Γ) (labels : List (Syntax Γ))
    (hs : LowerSupport Γ C lower) (p : CommonHeadLargeGuards.Formula) :
    ∀ i ∈ (translateGuard Γ lower labels p).variables,
      i ∈ labelSupport Γ C labels := by
  induction p with
  | truth => intro i hi; cases hi
  | falsity => intro i hi; cases hi
  | eq j k =>
    intro i hi
    rcases List.mem_append.mp (hs _ _ 0 i hi) with hj | hk
    · exact label_support Γ C labels j i hj
    · exact label_support Γ C labels k i hk
  | lt j k =>
    intro i hi
    rcases List.mem_append.mp (hs _ _ (-1) i hi) with hj | hk
    · exact label_support Γ C labels j i hj
    · exact label_support Γ C labels k i hk
  | bound c j =>
    intro i hi
    have hp := hs (label Γ labels j) (Affine.numeral Γ c) (-1) i hi
    rw [rawVariables_numeral, List.append_nil] at hp
    exact label_support Γ C labels j i hp
  | neg p ih => exact ih
  | conj p q ihp ihq =>
    intro i hi
    rcases List.mem_append.mp hi with hp | hq
    · exact ihp i hp
    · exact ihq i hq
  | disj p q ihp ihq =>
    intro i hi
    rcases List.mem_append.mp hi with hp | hq
    · exact ihp i hp
    · exact ihq i hq

/-- Exact translation for genuine, support-positive lower labels, together
with independent structural support containment. -/
theorem exactGuardTranslation : Targets.ExactGuardTranslation :=
  ⟨translate_eval, translate_support⟩

private theorem source_label_support (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E F : Upper k) (i : Nat)
    (hi : i ∈ labelSupport Γ C.1 (BalancedLargeGuards.sourceTerms k Γ C E F)) :
    i ∈ BalancedLargeGuards.sourceAmbient k Γ C E F := by
  obtain ⟨T, hT, hi⟩ := List.mem_flatMap.mp hi
  exact BalancedLargeGuards.Proof.sourceTerms_support k Γ C E F T hT i hi

/-- Accepted complete-input and lower-part labels instantiate the generic
translation under the actual C.1 and the unchanged raw valuation. -/
theorem actualSourceDescent : Targets.ActualSourceDescent := by
  constructor
  · intro k Γ C E F desired lower ν hC hE hF hpos hc
    have hg := BalancedLargeGuards.Proof.sourceTerms_genuine k Γ C E F hC
    have hlpos : ∀ i ∈ labelSupport Γ C.1 (BalancedLargeGuards.sourceTerms k Γ C E F),
        0 < ν i := by
      intro i hi
      exact hpos i (source_label_support k Γ C E F i hi)
    have ht : (sourceTranslation k Γ C E F desired lower).eval ν ↔
        (BalancedLargeGuards.sourceFormula E F desired).eval
          (BalancedLargeGuards.sourceValuation k Γ C E F ν) :=
      translate_eval Γ C.1 lower (BalancedLargeGuards.sourceTerms k Γ C E F)
        ν hc hg hlpos (BalancedLargeGuards.sourceFormula E F desired)
    exact ⟨ht, ht.trans (BalancedLargeGuards.Proof.exactActualSourceLargeFormula
      k Γ C E F desired ν hE hF)⟩
  · intro k Γ C E F desired lower hs i hi
    apply source_label_support k Γ C E F i
    exact translate_support Γ C.1 lower (BalancedLargeGuards.sourceTerms k Γ C E F)
      hs (BalancedLargeGuards.sourceFormula E F desired) i hi

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescent.Proof
