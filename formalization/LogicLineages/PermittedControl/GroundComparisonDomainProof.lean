module
public import LogicLineages.PermittedControl.GroundComparisonDomainTargets
import LogicLineages.PermittedControl.SourceScalarCalibrationProof
import LogicLineages.PermittedControl.SelectedGradedPositivityProof
import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

public section
namespace LogicLineages.PermittedControl.GroundComparisonDomain
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation
open SelectedSourceDomain

private def numeral : Nat → ClosedExpression
  | 0 => .one
  | n+1 => .add (numeral n) .one

private theorem numeral_grade (ctrl : Nat → Nat) (n i : Nat) : ClosedGrade ctrl i (numeral n) := by
  induction n with
  | zero => exact .one i
  | succ n ih => exact .add ih (.one i)

private theorem numeral_value (ctrl : Nat → Nat) (n : Nat) :
    closedValue ctrl (numeral n) = ((n+1 : Nat) : Ordinal) := by
  induction n with
  | zero =>
    change (1 : Ordinal) = ((0+1 : Nat) : Ordinal)
    simp
  | succ n ih =>
    change ordinalNaturalSum (closedValue ctrl (numeral n)) 1 = _
    rw [ih]
    simpa only [Nat.cast_one] using
      LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof.naturalSum_finite (n+1) 1

private theorem variable_ground {Γ : List Ty} {τ : Ty} (x : Variable Γ τ)
    (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) : τ=Ty.ground := by
  induction x with
  | here => exact hΓ _ (by simp)
  | there x ih => exact ih (fun σ h => hΓ σ (by simp [h]))

private theorem index_zero {Γ : List Ty} {τ : Ty} (x : Variable Γ τ)
    (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (j : Fin (τ.level+1)) : j=0 := by
  have ht := variable_ground x hΓ
  subst τ
  apply Fin.ext
  have hj := j.isLt
  change j.val<1 at hj
  change j.val=0
  omega

theorem selectedGroundDomain : SelectedGroundDomain := by
  classical
  intro ctrl K hctrl
  constructor
  · intro Γ hΓ ρ hp
    let s : AdmissibleSubstitution ctrl Γ := {
      vector := fun {τ} x j => numeral (ρ ⟨τ,x,j⟩-1)
      graded := fun x j => numeral_grade ctrl _ _
      bounded := by
        intro τ x j
        rw [index_zero x hΓ j]
    }
    refine ⟨s, ?_⟩
    rintro ⟨τ,x,j⟩
    change closedValue ctrl (numeral (ρ ⟨τ,x,j⟩-1)) = _
    rw [numeral_value, Nat.sub_add_cancel (hp _)]
  · intro Γ hΓ s
    have hf : ∀ c : OrdinalComponent Γ, ∃ n : Nat, 0<n ∧ valuation ctrl s c=(n : Ordinal) := by
      rintro ⟨τ,x,j⟩
      have hj := index_zero x hΓ j
      subst j
      have hg := s.graded x 0
      obtain ⟨n,hn⟩ := SourceScalarCalibrationProof.closed_scalar_finite ctrl hg rfl
      have hpos := SelectedGradedPositivityProof.closed_positive ctrl K hctrl hg
      refine ⟨n,?_,hn⟩
      rw [hn] at hpos
      exact_mod_cast hpos
    choose ρ hp hv using hf
    exact ⟨ρ,hp,hv⟩

#print axioms selectedGroundDomain
end LogicLineages.PermittedControl.GroundComparisonDomain
