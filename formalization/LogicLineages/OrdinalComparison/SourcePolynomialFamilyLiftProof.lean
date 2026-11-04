module
public import LogicLineages.OrdinalComparison.SourcePolynomialFamilyLiftTargets
public import LogicLineages.OrdinalComparison.SourceUnaryNormPaddingProof

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.SourcePolynomialFamilyLift.Proof

open OriginalDomain SourcePolynomialRealization

theorem simultaneousExtension : Targets.SimultaneousExtension := by
  intro Γ ρ n
  induction n with
  | zero =>
      intro p hp
      exact ⟨ρ, fun i => Fin.elim0 i, fun _ _ _ => rfl⟩
  | succ n ih =>
      intro p hp
      obtain ⟨τ, hτ, hold⟩ := ih (fun j => p j.succ) (fun j => hp j.succ)
      obtain ⟨σ, hc, hpos, hbound, hpad, hpres⟩ :=
        SourceUnaryNormPadding.Proof.polynomialExtension _ τ (p 0) (hp 0)
      refine ⟨σ, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [prefixVariable, Fin.cases_zero] using And.intro hc ⟨hpos, hbound, hpad⟩
        · simpa only [prefixVariable, Fin.cases_succ, hpres] using hτ j
      · intro υ x j
        change σ.vector (.there (oldVariable Γ υ n x)) j = ρ.vector x j
        rw [hpres]
        exact hold υ x j

private def emptySubstitution : AdmissibleSubstitution [] where
  vector := fun x => nomatch x
  graded := by intro τ x; cases x
  bounded := by intro τ x; cases x

theorem signedInputCalibration : Targets.SignedInputCalibration := by
  intro n
  induction n with
  | zero =>
      intro p hp
      exact ⟨emptySubstitution, fun i => Fin.elim0 i⟩
  | succ n ih =>
      intro p hp
      obtain ⟨τ, hτ⟩ := ih (fun j => p j.succ) (fun j => hp j.succ)
      obtain ⟨σ, hc, hpos, hbound, hpad, hpres⟩ :=
        SourceUnaryNormPadding.Proof.polynomialExtension _ τ (p 0) (hp 0)
      refine ⟨σ, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [SignedPair.inputs, SignedPair.inputVariable, Fin.cases_zero] using
          And.intro hc ⟨hpos, hbound, hpad⟩
      · simpa only [SignedPair.inputs, SignedPair.inputVariable, Fin.cases_succ, hpres] using hτ j

end LogicLineages.OrdinalComparison.Source.SourcePolynomialFamilyLift.Proof
