module
public import LogicLineages.CartierObserverCurrent.NaturalityTargets
public import LogicLineages.CartierObserverCurrent.MixedProperProof
public meta import LogicLineages.Audit

@[expose] public section
universe u v
namespace LogicLineages.CartierObserverCurrent.Naturality

theorem extensionInjective : Targets.ExtensionInjective.{u,v} := by
  intro K L _ _ σ
  exact (rationalMap σ).injective

theorem extensionPolynomial : Targets.ExtensionPolynomial.{u,v} := by
  intro K L _ _ σ P
  unfold rationalMap
  exact IsFractionRing.lift_algebraMap _ P

theorem extensionStep : Targets.ExtensionStep.{u,v} := by
  intro K L _ _ _ _ _ _ σ b f
  let E := rationalMap σ
  have hX : E (Basic.rationalX : RatFunc K) = (Basic.rationalX : RatFunc L) := by
    have h := extensionPolynomial K L σ Polynomial.X
    simpa only [Polynomial.map_X] using h
  have he : E f = (E (Basic.actualRationalSquareRootDigit false f)) ^ 2 +
      Basic.rationalX * (E (Basic.actualRationalSquareRootDigit true f)) ^ 2 := by
    have h := congrArg E (Basic.actualRationalSquareRootDecomposition K f)
    simpa only [map_add, map_mul, map_pow, hX] using h
  have hu := Basic.actualRationalSquareRootUniqueness L _ _ _ _
    (he.symm.trans (Basic.actualRationalSquareRootDecomposition L (E f)))
  rw [MixedProper.stepDigitIdentity, MixedProper.stepDigitIdentity]
  cases b
  · exact hu.1
  · exact hu.2

theorem extensionWord : Targets.ExtensionWord.{u,v} := by
  intro K L _ _ _ _ _ _ σ w
  induction w with
  | nil => intro f; rfl
  | cons b w ih =>
    intro f
    simp only [MixedWord.execute]
    rw [ih, extensionStep]

#audit_namespace LogicLineages.CartierObserverCurrent.Naturality
end LogicLineages.CartierObserverCurrent.Naturality
