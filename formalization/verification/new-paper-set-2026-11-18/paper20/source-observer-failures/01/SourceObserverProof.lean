module
public import LogicLineages.CartierObserverCurrent.SourceObserverTargets
public import LogicLineages.CartierObserverCurrent.SourceStateProof
public import LogicLineages.CartierObserverCurrent.AllWordObserverProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.SourceObserver
open SplittingRoots

theorem presentedExpansion : Targets.PresentedExpansion := by
  intro d P
  have hA : (SourceBudget.denominator (ZMod 2) d).eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, SourceBudget.sourceConstant]
    exact one_ne_zero
  have hf : RegularSelectors.regular (initial d P) := by
    obtain ⟨Q, hQ⟩ := RatFunc.denom_div_dvd P (SourceBudget.denominator (ZMod 2) d)
    intro h
    apply hA
    rw [hQ, Polynomial.eval_mul, h, zero_mul]
  refine ⟨hf, ?_⟩
  apply FractionSeries.representationIndependent (ZMod 2)
    (initial d P).num (initial d P).denom P (SourceBudget.denominator (ZMod 2) d)
  · simpa only [RegularSelectors.regular, Polynomial.coeff_zero_eq_eval_zero] using hf
  · simpa only [Polynomial.coeff_zero_eq_eval_zero] using hA
  · exact (initial d P).num_div_denom

theorem exactSourceContinuations : Targets.ExactSourceContinuations := by
  intro d hd P hP p hp
  let g := MixedWord.execute p (initial d P)
  have hs := SourceState.transientState d hd P hP p hp
  have he : ProfileDescent.extend d g = SourceState.run d P p := rfl
  have hg : ProfileDescent.baseState d g := by
    constructor
    · apply (CanonicalExtension.properMap (ZMod 2) (FieldAt d) (algebraMap (ZMod 2) (FieldAt d)) g).mp
      exact hs.1
    · exact hs.2
  obtain ⟨b, ⟨hb, hrec⟩, _⟩ := ProfileDescent.baseToProfile d g hg
  refine ⟨b, ⟨hb, hrec.trans he, ?_⟩, ?_⟩
  · intro w
    rw [AllWordObserver.baseObservation d g b hrec.symm]
    have hc := AllWordObserver.wordCoefficient (initial d P) (presentedExpansion d P).1 p
      (AllWordObserver.offset w)
    change (RegularSelectors.expansion g).coeff _ = _ at hc
    rw [hc, (presentedExpansion d P).2, Nat.add_comm]
  · intro c hc
    exact RationalCoverage.reconstructionInjective d (hc.2.1.trans (hrec.trans he).symm)

#audit_namespace LogicLineages.CartierObserverCurrent.SourceObserver
end LogicLineages.CartierObserverCurrent.SourceObserver
