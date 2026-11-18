module
public import LogicLineages.CartierObserverCurrent.FullScalarProfileTargets
public import LogicLineages.CartierObserverCurrent.RepeatedCartierProof
public import LogicLineages.CartierObserverCurrent.ProfileOutputProof
public import LogicLineages.CartierObserverCurrent.NaturalityProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullScalarProfile
open SplittingRoots

theorem initialMeaning : Targets.InitialMeaning := by
  intro d hd P hP
  exact Classical.choose_spec (InitialPrincipalParts.initialSourceCoverage d hd P hP)

private theorem extension_iterate (d ell : Nat) (f : RatFunc (ZMod 2)) :
    ProfileDescent.extend d ((Basic.actualDifferentialCartier (K := ZMod 2))^[ell] f) =
      (Basic.actualDifferentialCartier (K := FieldAt d))^[ell] (ProfileDescent.extend d f) := by
  induction ell generalizing f with
  | zero => rfl
  | succ ell ih =>
    rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
    have h := Naturality.extensionStep (ZMod 2) (FieldAt d)
      (algebraMap (ZMod 2) (FieldAt d)) true f
    simpa only [ProfileDescent.extend, MixedProper.step, if_true] using
      congrArg ((Basic.actualDifferentialCartier (K := FieldAt d))^[ell]) h

private theorem initial_extension (d : Nat) (P : Polynomial (ZMod 2)) :
    ProfileDescent.extend d (SourceObserver.initial d P) = InitialPrincipalParts.source d P := by
  unfold ProfileDescent.extend SourceObserver.initial FractionSeries.rationalFraction
  rw [map_div₀, Naturality.extensionPolynomial, Naturality.extensionPolynomial]
  rfl

theorem actualIterate : Targets.ActualIterate := by
  intro d hd P hP ell hEll
  rw [extension_iterate, initial_extension, ← (initialMeaning d hd P hP).1]
  have hM := (SourceBudget.positiveBudgetTransient d hd).1
  have hbound : SourceBudget.budget d ≤ 2 ^ ell :=
    (SourceBudget.positiveBudgetTransient d hd).2.trans (Nat.pow_le_pow_right (by decide) hEll)
  exact RepeatedCartier.principalReduction d (SourceBudget.budget d) hM
    (initialCoefficients d hd P hP) ell hbound

theorem scalarOutput : Targets.ScalarOutput := by
  intro d hd P hP ell hEll
  exact ProfileOutput.actualBaseOutput d _ _ (actualIterate d hd P hP ell hEll)

theorem completeScalarProfile : Targets.CompleteScalarProfile :=
  ⟨initialMeaning, actualIterate, scalarOutput⟩

#audit_namespace LogicLineages.CartierObserverCurrent.FullScalarProfile
end LogicLineages.CartierObserverCurrent.FullScalarProfile
