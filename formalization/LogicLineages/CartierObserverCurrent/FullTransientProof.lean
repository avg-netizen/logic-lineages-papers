module
public import LogicLineages.CartierObserverCurrent.FullTransientTargets
public import LogicLineages.CartierObserverCurrent.SourceBudgetProof
public import LogicLineages.CartierObserverCurrent.MixedWordProof
public meta import LogicLineages.Audit

@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.FullTransient

theorem binaryTransient : Targets.BinaryTransient.{u,v} := by
  refine ⟨MixedProper.stepProper, PoleContraction.canonicalPoleContraction,
    PoleContraction.noNewPole, ?_⟩
  intro K L _ _ _ _ _ _ σ d hd P hP w
  let f : RatFunc K := algebraMap (Polynomial K) (RatFunc K) P /
    algebraMap (Polynomial K) (RatFunc K) (SourceBudget.denominator K d)
  let fL : RatFunc L := algebraMap (Polynomial L) (RatFunc L) (P.map σ) /
    algebraMap (Polynomial L) (RatFunc L) (SourceBudget.denominator L d)
  have hm := SourceBudget.mappedProperInput K L σ d P hP
  have hmap : Naturality.rationalMap σ f = fL := hm.2.1
  have hproper : MixedProper.proper fL := hm.2.2
  have hword : Naturality.rationalMap σ (MixedWord.execute w f) = MixedWord.execute w fL := by
    rw [Naturality.extensionWord, hmap]
  change MixedProper.proper (Naturality.rationalMap σ (MixedWord.execute w f)) ∧
    (∀ z : L, PoleContraction.poleOrder z (Naturality.rationalMap σ f) = 0 →
      PoleContraction.poleOrder z (Naturality.rationalMap σ (MixedWord.execute w f)) = 0) ∧
    (SourceBudget.transient d ≤ w.length → ∀ z : L,
      PoleContraction.poleOrder z (Naturality.rationalMap σ (MixedWord.execute w f)) ≤ 1)
  rw [hword, hmap]
  refine ⟨MixedWord.wordProper L w fL hproper, MixedWord.wordNoNewPole L w fL, ?_⟩
  intro hlen z
  have hA : SourceBudget.denominator L d ≠ 0 := by
    intro hz
    have hc := SourceBudget.sourceConstant L d
    simpa only [hz, Polynomial.coeff_zero, zero_ne_one] using hc
  have hdiv : fL.denom ∣ SourceBudget.denominator L d := RatFunc.denom_div_dvd _ _
  have hord : PoleContraction.poleOrder z fL ≤ SourceBudget.budget d :=
    (Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hA hdiv z).trans
      (SourceBudget.sourceMultiplicity L d z)
  apply MixedWord.wordOrderBound L w fL z 1
  calc
    PoleContraction.poleOrder z fL ≤ SourceBudget.budget d := hord
    _ ≤ 2 ^ SourceBudget.transient d := (SourceBudget.positiveBudgetTransient d hd).2
    _ ≤ 1 * 2 ^ w.length := by
      simpa only [one_mul] using Nat.pow_le_pow_right (by decide : 0 < 2) hlen

#audit_namespace LogicLineages.CartierObserverCurrent.FullTransient
end LogicLineages.CartierObserverCurrent.FullTransient
