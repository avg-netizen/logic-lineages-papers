module
public import LogicLineages.PermittedControl.SelectedPolynomialPaddingProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedPolynomialLift.Proof
open OrdinalComparison Source SelectedSourceDomain SourcePolynomialRealization SourcePolynomialFamilyLift

theorem simultaneousExtension : SelectedPolynomialLiftTargets.SimultaneousExtension := by
  intro ctrl Γ ρ n
  induction n with
  | zero =>
      intro p hp
      exact ⟨ρ, fun i => Fin.elim0 i, fun _ _ _ => rfl⟩
  | succ n ih =>
      intro p hp
      obtain ⟨τ, hτ, hold⟩ := ih (fun j => p j.succ) (fun j => hp j.succ)
      obtain ⟨σ, hc, hpos, hbound, hpad, hpres⟩ :=
        polynomialExtension ctrl _ τ (p 0) (hp 0)
      refine ⟨σ, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [prefixVariable, Fin.cases_zero] using And.intro hc ⟨hpos, hbound, hpad⟩
        · simpa only [prefixVariable, Fin.cases_succ, hpres] using hτ j
      · intro υ x j
        change σ.vector (.there (oldVariable Γ υ n x)) j = ρ.vector x j
        rw [hpres]
        exact hold υ x j

private def emptySubstitution (ctrl : Nat → Nat) : AdmissibleSubstitution ctrl [] where
  vector := fun x => nomatch x
  graded := by intro τ x; cases x
  bounded := by intro τ x; cases x

theorem signedInputCalibration : SelectedPolynomialLiftTargets.SignedInputCalibration := by
  intro ctrl n
  induction n with
  | zero =>
      intro p hp
      exact ⟨emptySubstitution ctrl, fun i => Fin.elim0 i⟩
  | succ n ih =>
      intro p hp
      obtain ⟨τ, hτ⟩ := ih (fun j => p j.succ) (fun j => hp j.succ)
      obtain ⟨σ, hc, hpos, hbound, hpad, hpres⟩ :=
        polynomialExtension ctrl _ τ (p 0) (hp 0)
      refine ⟨σ, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [SelectedPairCompiler.inputs, SignedPair.inputVariable, Fin.cases_zero] using
          And.intro hc ⟨hpos, hbound, hpad⟩
      · simpa only [SelectedPairCompiler.inputs, SignedPair.inputVariable, Fin.cases_succ, hpres] using hτ j

theorem selectedPolynomialLift : SelectedPolynomialLiftTargets.SelectedPolynomialLift :=
  ⟨gradedRealization,exactPaddedVector,simultaneousExtension,signedInputCalibration⟩
end LogicLineages.PermittedControl.SelectedPolynomialLift.Proof
