module
public import LogicLineages.PermittedControl.SelectedPolynomialLiftTargets
public import LogicLineages.PermittedControl.SelectedDetectorFactsProof
public import LogicLineages.OrdinalComparison.SourcePolynomialRealizationProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedPolynomialLift.Proof
open OrdinalComparison Source SelectedSourceDomain SourcePolynomialRealization

private theorem monomial_graded (ctrl : Nat → Nat) (n k : Nat) (hk : k ≠ 0) :
    ∃ t : ClosedExpression, ClosedGrade ctrl 1 t ∧
      SignedPair.signedCNF (closedValue ctrl t) = Finsupp.single (n : Ordinal) (k : Int) := by
  induction n with
  | zero =>
      refine ⟨UnitObservation.positive (k-1),
        ClosedGrade.promote (by decide) (SelectedFunctionalDetector.positiveGrade ctrl (k-1)), ?_⟩
      rw [SelectedFunctionalDetector.Proof.positiveValue ctrl, show k-1+1=k by omega]
      simpa only [Nat.cast_zero] using SignedPair.Proof.cnf_nat k
  | succ n ih =>
      obtain ⟨t, ht, hc⟩ := ih
      refine ⟨.emul .omega t, ClosedGrade.emul (by decide) (ClosedGrade.omega 2 (by decide)) ht, ?_⟩
      have hv : closedValue ctrl (.emul .omega t) = ordinalNaturalProduct Ordinal.omega0 (closedValue ctrl t) := by
        change ordinalNaturalProduct ((2 : Ordinal)^Ordinal.omega0) (closedValue ctrl t) = _
        have hp : (2 : Ordinal)^Ordinal.omega0 = Ordinal.omega0 := by
          simpa using Ordinal.natCast_opow_omega0 (by decide : 1 < (2 : Nat))
        rw [hp]
      rw [hv, SignedPair.Proof.cnf_omega_product _ (SelectedValueClosureProof.closed_below ctrl t), hc]
      simp only [SignedPair.omegaShift, Finsupp.mapDomain_single, Nat.cast_succ]

private theorem embedded_single (n k : Nat) :
    embeddedCoefficients (Finsupp.single n k) = Finsupp.single (n : Ordinal) (k : Int) := by
  simp only [embeddedCoefficients, signedCoefficients, Finsupp.mapRange_single,
    Finsupp.mapDomain_single]

private theorem embedded_add (p q : NonnegativePolynomial) :
    embeddedCoefficients (p+q) = embeddedCoefficients p + embeddedCoefficients q := by
  have hs : signedCoefficients (p+q) = signedCoefficients p + signedCoefficients q := by
    ext n
    simp [signedCoefficients, Nat.cast_add]
  unfold embeddedCoefficients
  rw [hs, Finsupp.mapDomain_add]

theorem gradedConstruction (ctrl : Nat → Nat) (p : NonnegativePolynomial) : p ≠ 0 →
    ∃ t : ClosedExpression, ClosedGrade ctrl 1 t ∧
      SignedPair.signedCNF (closedValue ctrl t) = embeddedCoefficients p := by
  classical
  induction p using Finsupp.induction with
  | zero =>
      intro hp
      exact False.elim (hp rfl)
  | single_add n k p hn hk ih =>
      intro _
      obtain ⟨s, hs, hsc⟩ := monomial_graded ctrl n k hk
      by_cases hp : p = 0
      · subst p
        refine ⟨s, hs, ?_⟩
        simpa only [add_zero, embedded_single] using hsc
      · obtain ⟨t, ht, htc⟩ := ih hp
        refine ⟨.add s t, ClosedGrade.add hs ht, ?_⟩
        change SignedPair.signedCNF (ordinalNaturalSum (closedValue ctrl s) (closedValue ctrl t)) = _
        rw [SignedPair.Proof.cnf_sum, hsc, htc, embedded_add, embedded_single]

private theorem signedCNF_injective : Function.Injective SignedPair.signedCNF := by
  intro a b hab
  apply Ordinal.CNF.coeff_injective Ordinal.omega0
  ext e
  have h := congrArg (fun g : SignedPair.CantorGroup => g e) hab
  simp only [SignedPair.Proof.cnf_apply] at h
  obtain ⟨m,hm⟩ := Ordinal.lt_omega0.mp (FunctionalDetector.Proof.coeff_finite a e)
  obtain ⟨n,hn⟩ := Ordinal.lt_omega0.mp (FunctionalDetector.Proof.coeff_finite b e)
  rw [hm,hn,SignedPair.Proof.finite_nat,SignedPair.Proof.finite_nat] at h
  have he : m=n := by exact_mod_cast h
  rw [hm,hn,he]

theorem gradedRealization : SelectedPolynomialLiftTargets.GradedRealization := by
  intro ctrl p hp
  obtain ⟨t,ht,hcnf⟩ := gradedConstruction ctrl p hp
  obtain ⟨a,ha,hac,hproj,hzero,hpos⟩ := SourcePolynomialRealization.Proof.actualRealization p
  have he : closedValue ctrl t=a := signedCNF_injective (hcnf.trans hac.symm)
  refine ⟨t,ht,hcnf,?_,?_⟩
  · rw [he]
    exact hpos.mpr hp
  · rw [he]
    exact ha
end LogicLineages.PermittedControl.SelectedPolynomialLift.Proof
