module

public import LogicLineages.NativeModule.PersistentMarking.NativeTowerSequenceTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeTowerPrintedProof

@[expose] public section

/-! Each native tower term `t_n` of (D) is closed native and realizes the paper's composite
`Δ_n'`, by induction over the application spine `B_l B_{l-1} ⋯ B_0`, from the printed tower
realization (#1459) and the literal arithmetic realizers (`Next = fix pow`, `ω`). Realization of
an application is the definition of arrow realization. -/

namespace LogicLineages.PersistentMarking.NativeTowerSequenceProof
open Spine NativeReduction NativeIndexedCarrierTargets NativeIteratorStrictTargets
open OrdinalRealizationTargets NativeOrdinalRealizationTargets OrdinalArithmeticRealizationTargets
open NativeTowerTargets NativeTowerSequenceTargets NativeOrdinalArithmeticCompositionTargets
open NativeTowerProof (wfOf)

theorem downRealizes (S : Signature) (fix : Value (tier 2))
    (hB : ∀ k, ∃ t : (nativeTerms S).term (tier (k+2)), t.val = towerB k ∧
      Realizes (nativeTerms S) (wfOf S) (tier (k+2)) t (towerValue fix k)) :
    ∀ k (v : (nativeTerms S).term (tier (k+2))) (y : Value (tier (k+2))),
      Realizes (nativeTerms S) (wfOf S) (tier (k+2)) v y →
      ∃ c : (nativeTerms S).term (tier 2), c.val = downTerm k v.val ∧
        Realizes (nativeTerms S) (wfOf S) (tier 2) c (downValue fix k y) := by
  intro k
  induction k with
  | zero => exact fun v y hv => ⟨v, rfl, hv⟩
  | succ k ih =>
    intro v y hv
    obtain ⟨b, hb, hbr⟩ := hB k
    obtain ⟨c, hc, hcr⟩ := ih _ _ (hv _ b hbr)
    refine ⟨c, ?_, hcr⟩
    rw [hc]
    show downTerm k (app (tierType (k+2)) (tierType (k+2)) v.val b.val) = _
    rw [hb]
    rfl

theorem exact_NativeTowerSequenceRealization : NativeTowerSequenceRealization := by
  intro S
  obtain ⟨_, printed⟩ := NativeTowerPrintedProof.exact_PrintedTowerRealization S
  obtain ⟨_, arithmetic⟩ := NativeOrdinalArithmeticCompositionProof.exact_LiteralNativeArithmeticRealizes S
  refine ⟨wfOf S, ?_⟩
  intro Z s add mul w one pow fix h1 h2 n
  have hB : ∀ k, ∃ t : (nativeTerms S).term (tier (k+2)), t.val = towerB k ∧
      Realizes (nativeTerms S) (wfOf S) (tier (k+2)) t (towerValue fix k) :=
    fun k => printed Z s add mul w one pow fix h1 h2 k
  have ops := arithmetic Z s add mul w one pow fix h1 h2
  let op := literalArithmetic S
  have hω : Realizes (nativeTerms S) (wfOf S) .base op.omega w := ops.2.2.2.2.1
  have hNext : Realizes (nativeTerms S) (wfOf S) (tier 1) (literalNext op) (fix pow) :=
    ops.2.2.2.2.2.2.2.2
  obtain ⟨b0, hb0, hb0r⟩ := hB 0
  obtain ⟨b1, hb1, hb1r⟩ := hB 1
  let NB : (nativeTerms S).term (tier 1) :=
    (nativeTerms S).app (tier 1) (tier 1) ((nativeTerms S).app (tier 2) (tier 2) b1 b0) (literalNext op)
  have hNB : Realizes (nativeTerms S) (wfOf S) (tier 1) NB (veblenValue fix pow) :=
    hb1r _ b0 hb0r (fix pow) (literalNext op) hNext
  have hNBval : NB.val = veblenTerm := by
    show app (tierType 1) (tierType 1) (app (tierType 2) (tierType 2) b1.val b0.val) (literalNext op).val = _
    rw [hb1, hb0]
    rfl
  let E : (nativeTerms S).term .base := (nativeTerms S).app .base .base NB op.omega
  have hE : Realizes (nativeTerms S) (wfOf S) .base E (baseValue fix pow w) := hNB w op.omega hω
  have hEval : E.val = baseTerm := by
    show app indexType indexType NB.val op.omega.val = _
    rw [hNBval]
    rfl
  match n with
  | 0 => exact ⟨E, hEval, hE⟩
  | 1 =>
    refine ⟨(nativeTerms S).app .base .base NB E, ?_, hNB _ E hE⟩
    show app indexType indexType NB.val E.val = _
    rw [hNBval, hEval]
    rfl
  | l + 2 =>
    obtain ⟨bl, hbl, hblr⟩ := hB l
    obtain ⟨c, hc, hcr⟩ := downRealizes S fix hB l bl _ hblr
    refine ⟨(nativeTerms S).app .base .base ((nativeTerms S).app (tier 1) (tier 1) c NB) E, ?_,
      hcr _ NB hNB _ E hE⟩
    show app indexType indexType (app (tierType 1) (tierType 1) c.val NB.val) E.val = _
    rw [hc, hbl, hNBval, hEval]
    rfl

/-! Faithfulness checks against the printed (D). -/

theorem sequenceTerm_zero :
    sequenceTerm 0 = app indexType indexType
      (app (tierType 1) (tierType 1) (app (tierType 2) (tierType 2) (towerB 1) (towerB 0))
        NativeOrdinalExponentialTargets.ordinalNext) NativeOrdinalBasisTargets.omegaCarrier :=
  rfl

theorem sequenceTerm_one :
    sequenceTerm 1 = app indexType indexType veblenTerm
      (app indexType indexType veblenTerm NativeOrdinalBasisTargets.omegaCarrier) :=
  rfl

theorem sequenceTerm_two :
    sequenceTerm 2 = app indexType indexType (app (tierType 1) (tierType 1) (towerB 0) veblenTerm) baseTerm :=
  rfl

theorem sequenceTerm_three :
    sequenceTerm 3 = app indexType indexType
      (app (tierType 1) (tierType 1) (app (tierType 2) (tierType 2) (towerB 1) (towerB 0)) veblenTerm)
      baseTerm :=
  rfl

theorem sequenceValue_zero (fix : Value (tier 2)) (pow : Value (tier 1)) (w : CountableOrdinal) :
    sequenceValue fix pow w 0 = towerValue fix 1 (towerValue fix 0) (fix pow) w := rfl

theorem sequenceValue_three (fix : Value (tier 2)) (pow : Value (tier 1)) (w : CountableOrdinal) :
    sequenceValue fix pow w 3 =
      towerValue fix 1 (towerValue fix 0) (veblenValue fix pow) (baseValue fix pow w) := rfl

#print axioms exact_NativeTowerSequenceRealization

end LogicLineages.PersistentMarking.NativeTowerSequenceProof
