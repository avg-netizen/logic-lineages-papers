module
public import LogicLineages.OrdinalComparison.WWRawPartialTargets
public import LogicLineages.OrdinalComparison.WWTypedPartialProof
public import LogicLineages.OrdinalComparison.WWTypedComponentProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem actualTypedHeadReplacementCalibration : Targets.ActualTypedHeadReplacementCalibration := by
  intro Γ σ t
  induction t with
  | var c =>
    rcases c with ⟨τ, v, i⟩
    cases v <;> rfl
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add f g hf hg | emul f g hf hg | collapse f g hf hg =>
    simp_all [ordinalHeadReplacement, ordinalHeadClosure, ordinalExpressionRename, substitute]

private theorem raw_free_case {Γ : List Ty} {σ : Ty} (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) (h : ordinalHeadFree t = true) :
    ordinalRawPartial i t = (ordinalTypedPartial i t).map ordinalPartialWeaken := by
  rw [ordinalRawPartial.eq_def, h, actualTypedFreePartial Γ σ i t h]
  simp only [Bool.true_eq, if_true, Option.map_some]
  congr 1
  funext j
  have hc := (actualTypedHeadFreeCalibration Γ σ t).mp h
  by_cases hij : i = j.val <;>
    simp [ordinalPartialWeaken, ordinalFreePartialVector, hij, ordinalExpressionRename,
      substitute] at hc ⊢
  exact hc.symm

theorem actualRawPartialErasureCalibration : Targets.ActualRawPartialErasureCalibration := by
  intro Γ σ i t
  induction t generalizing i with
  | zero => exact raw_free_case i _ rfl
  | one => exact raw_free_case i _ rfl
  | omega => exact raw_free_case i _ rfl
  | var c =>
    by_cases h : ordinalHeadFree (.var c) = true
    · exact raw_free_case i _ h
    · rw [ordinalRawPartial, ordinalTypedPartial]
      simp only [h, Bool.false_eq_true, ↓reduceIte]
      rcases c with ⟨τ, v, k⟩
      split <;> simp [ordinalPartialWeaken, ordinalExpressionRename, substitute]
      rfl
  | add f g hf hg =>
    by_cases h : ordinalHeadFree (.add f g) = true
    · exact raw_free_case i _ h
    · rw [ordinalRawPartial, ordinalTypedPartial]
      simp only [h, Bool.false_eq_true, ↓reduceIte, hf, hg]
      cases hp : ordinalTypedPartial i f <;> cases hq : ordinalTypedPartial i g <;>
        simp [ordinalPartialWeaken, ordinalExpressionRename, substitute]
      rfl
  | emul f g hf hg =>
    by_cases h : ordinalHeadFree (.emul f g) = true
    · exact raw_free_case i _ h
    · rw [ordinalRawPartial, ordinalTypedPartial]
      simp only [h, Bool.false_eq_true, ↓reduceIte]
      split
      · rw [hf, hg]
        cases hp : ordinalTypedPartial (i + 1) f <;> cases hq : ordinalTypedPartial i g <;>
          simp [ordinalPartialWeaken, ordinalExpressionRename, substitute]
        rfl
      · rfl
  | collapse f g hf hg =>
    by_cases h : ordinalHeadFree (.collapse f g) = true
    · exact raw_free_case i _ h
    · rw [ordinalRawPartial, ordinalTypedPartial]
      simp only [h, Bool.false_eq_true, ↓reduceIte]
      split
      · rw [hf, hg]
        cases hp : ordinalTypedPartial 1 f <;> cases hq : ordinalTypedPartial 0 g <;>
          simp [ordinalPartialWeaken, ordinalExpressionRename, substitute,
            actualTypedHeadReplacementCalibration Γ σ f]
        funext j
        by_cases hj : j = 0 <;>
          simp [ordinalPartialWeaken, ordinalExpressionRename, substitute, hj,
            actualTypedHeadReplacementCalibration Γ σ f]
      · rfl

theorem actualRawPartialHeadFreeRecovery : Targets.ActualRawPartialHeadFreeRecovery := by
  intro Γ σ i t v h
  rw [actualRawPartialErasureCalibration] at h
  cases hp : ordinalTypedPartial i t with
  | none => simp [hp] at h
  | some w =>
    simp only [hp, Option.map_some, Option.some.injEq] at h
    subst v
    constructor
    · intro j
      apply (actualTypedHeadFreeCalibration Γ σ _).mpr
      change ordinalExpressionRename (Renaming.weaken Γ σ)
        (ordinalHeadClosure (ordinalExpressionRename (Renaming.weaken Γ σ) (w j))) = _
      rw [(actualTypedOrdinalHeadClosure).2 Γ σ (w j)]
      rfl
    · congr 1
      funext j
      exact ((actualTypedOrdinalHeadClosure).2 Γ σ (w j)).symm

end LogicLineages.OrdinalComparison.Source
