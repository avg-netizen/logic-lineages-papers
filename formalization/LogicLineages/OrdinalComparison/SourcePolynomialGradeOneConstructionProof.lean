module
public import LogicLineages.OrdinalComparison.SourcePolynomialGradeOneTargets
public import LogicLineages.OrdinalComparison.WWUnitObservationProof
public import LogicLineages.OrdinalComparison.WWOriginalValueClosureProof
public import LogicLineages.OrdinalComparison.SourceSignedPairAlgebraProof

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.SourcePolynomialGradeOne.Proof

open OriginalDomain SourcePolynomialRealization

private theorem monomial_graded (n k : Nat) (hk : k ≠ 0) :
    ∃ t : ClosedExpression, ClosedGrade 1 t ∧
      SignedPair.signedCNF (closedValue t) = Finsupp.single (n : Ordinal) (k : Int) := by
  induction n with
  | zero =>
      refine ⟨UnitObservation.positive (k-1),
        ClosedGrade.promote (by decide) (UnitObservation.positiveGrade (k-1)), ?_⟩
      rw [UnitObservation.Proof.positiveValue, show k-1+1=k by omega]
      simpa only [Nat.cast_zero] using SignedPair.Proof.cnf_nat k
  | succ n ih =>
      obtain ⟨t, ht, hc⟩ := ih
      refine ⟨.emul .omega t, ClosedGrade.emul (by decide) (ClosedGrade.omega 2 (by decide)) ht, ?_⟩
      have hv : closedValue (.emul .omega t) = ordinalNaturalProduct Ordinal.omega0 (closedValue t) := by
        change ordinalNaturalProduct ((2 : Ordinal)^Ordinal.omega0) (closedValue t) = _
        have hp : (2 : Ordinal)^Ordinal.omega0 = Ordinal.omega0 := by
          simpa using Ordinal.natCast_opow_omega0 (by decide : 1 < (2 : Nat))
        rw [hp]
      rw [hv, SignedPair.Proof.cnf_omega_product _ (originalClosedValueBelowEpsilonZero t), hc]
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

theorem gradedConstruction (p : NonnegativePolynomial) : p ≠ 0 →
    ∃ t : ClosedExpression, ClosedGrade 1 t ∧
      SignedPair.signedCNF (closedValue t) = embeddedCoefficients p := by
  classical
  induction p using Finsupp.induction with
  | zero =>
      intro hp
      exact False.elim (hp rfl)
  | single_add n k p hn hk ih =>
      intro _
      obtain ⟨s, hs, hsc⟩ := monomial_graded n k hk
      by_cases hp : p = 0
      · subst p
        refine ⟨s, hs, ?_⟩
        simpa only [add_zero, embedded_single] using hsc
      · obtain ⟨t, ht, htc⟩ := ih hp
        refine ⟨.add s t, ClosedGrade.add hs ht, ?_⟩
        change SignedPair.signedCNF (ordinalNaturalSum (closedValue s) (closedValue t)) = _
        rw [SignedPair.Proof.cnf_sum, hsc, htc, embedded_add, embedded_single]

end LogicLineages.OrdinalComparison.Source.SourcePolynomialGradeOne.Proof
