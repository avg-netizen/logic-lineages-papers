module
public import LogicLineages.StandardControlCurrent.DefaultSourceTargets
public import LogicLineages.OrdinalComparison.WWOriginalDomainProof
public import LogicLineages.OrdinalComparison.WWOriginalPositivityProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.DefaultSourceDomainProof
open OrdinalComparison Source Source.OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

private def numeral : Nat → ClosedExpression
  | 0 => .one
  | n+1 => .add (numeral n) .one

private theorem numeral_grade (n i : Nat) : ClosedGrade i (numeral n) := by
  induction n with
  | zero => exact .one i
  | succ n ih => exact .add ih (.one i)

private theorem numeral_value (n : Nat) : closedValue (numeral n) = ((n+1 : Nat) : Ordinal) := by
  induction n with
  | zero => simp [numeral,closedValue,denote]
  | succ n ih =>
    change ordinalNaturalSum (closedValue (numeral n)) 1 = _
    rw [ih]
    exact naturalSum_finite (n+1) 1

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

theorem domain : DefaultSourceTargets.GroundDomain := by
  classical
  constructor
  · intro Γ hΓ ρ hp
    let s : AdmissibleSubstitution Γ := {
      vector := fun {τ} x j => numeral (ρ ⟨τ,x,j⟩-1)
      graded := fun x j => numeral_grade _ _
      bounded := by
        intro τ x j
        rw [index_zero x hΓ j]
    }
    refine ⟨s, ?_⟩
    rintro ⟨τ,x,j⟩
    change closedValue (numeral (ρ ⟨τ,x,j⟩-1)) = _
    rw [numeral_value, Nat.sub_add_cancel (hp _)]
  · intro Γ hΓ s
    have hf : ∀ c : OrdinalComponent Γ, ∃ n : Nat, 0<n ∧ valuation s c=(n : Ordinal) := by
      rintro ⟨τ,x,j⟩
      have hj := index_zero x hΓ j
      subst j
      have hg := s.graded x 0
      obtain ⟨n,hn⟩ := originalClosedScalarFinite _ hg
      have hp := originalClosedGradePositive 0 _ hg
      refine ⟨n,?_,hn⟩
      rw [hn] at hp
      exact_mod_cast hp
    choose ρ hp hv using hf
    exact ⟨ρ,hp,hv⟩
end LogicLineages.StandardControlCurrent.DefaultSourceDomainProof
