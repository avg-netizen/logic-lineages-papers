module
public import LogicLineages.PermittedControl.SelectedPolynomialConstructionProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedPolynomialLift.Proof
open OrdinalComparison Source SelectedSourceDomain SourcePolynomialRealization
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem exactPaddedVector : SelectedPolynomialLiftTargets.ExactPaddedVector := by
  intro ctrl t ht
  have hv : closedValue ctrl (vector ctrl t 0)=((actualOrdinalNorm (closedValue ctrl t)+1 : Nat) : Ordinal) :=
    SelectedFunctionalDetector.Proof.positiveValue ctrl (actualOrdinalNorm (closedValue ctrl t))
  have hn : actualOrdinalNorm (closedValue ctrl (vector ctrl t 0))=actualOrdinalNorm (closedValue ctrl t)+1 := by
    rw [hv]
    exact (finiteNorm _).2
  refine ⟨?_,?_,hv,rfl⟩
  · intro j
    by_cases hj : j.val=0
    · have he : j=0 := Fin.ext hj
      subst j
      exact SelectedFunctionalDetector.positiveGrade ctrl _
    · have hj1 : j.val=1 := by have hh := j.isLt; omega
      have he : j=1 := Fin.ext hj1
      subst j
      exact ht
  · intro j
    by_cases hj : j.val=0
    · have he : j=0 := Fin.ext hj
      subst j
      exact le_rfl
    · have hj1 : j.val=1 := by have hh := j.isLt; omega
      have he : j=1 := Fin.ext hj1
      subst j
      change actualOrdinalNorm (closedValue ctrl t)≤actualOrdinalNorm (closedValue ctrl (vector ctrl t 0))
      rw [hn]
      omega

theorem admissibleExtension (ctrl : Nat → Nat) (Γ : List Ty) (ρ : AdmissibleSubstitution ctrl Γ)
    (t : ClosedExpression) (ht : ClosedGrade ctrl 1 t) :
    ∃ σ : AdmissibleSubstitution ctrl (FunctionalDetector.unary::Γ),
      (∀ j : Fin 2, σ.vector .here j=vector ctrl t j) ∧
      (∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)), σ.vector (.there x) j=ρ.vector x j) := by
  have hv := exactPaddedVector ctrl t ht
  let σ : AdmissibleSubstitution ctrl (FunctionalDetector.unary::Γ) := {
    vector := fun x j => match x with
      | .here => vector ctrl t j
      | .there x => ρ.vector x j
    graded := by
      intro τ x j
      cases x with
      | here => exact hv.1 j
      | there x => exact ρ.graded x j
    bounded := by
      intro τ x j
      cases x with
      | here => exact hv.2.1 j
      | there x => exact ρ.bounded x j }
  exact ⟨σ,fun _ => rfl,fun _ _ _ => rfl⟩

theorem polynomialExtension (ctrl : Nat → Nat) (Γ : List Ty) (ρ : AdmissibleSubstitution ctrl Γ)
    (p : NonnegativePolynomial) (hp : p≠0) :
    ∃ σ : AdmissibleSubstitution ctrl (FunctionalDetector.unary::Γ),
      SignedPair.signedCNF (closedValue ctrl (σ.vector .here 1))=embeddedCoefficients p ∧
      0<closedValue ctrl (σ.vector .here 1) ∧
      closedValue ctrl (σ.vector .here 1)<Ordinal.omega0^Ordinal.omega0 ∧
      closedValue ctrl (σ.vector .here 0)=((actualOrdinalNorm (closedValue ctrl (σ.vector .here 1))+1 : Nat) : Ordinal) ∧
      (∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)),σ.vector (.there x) j=ρ.vector x j) := by
  obtain ⟨t,ht,hcnf,hpos,hbound⟩ := gradedRealization ctrl p hp
  obtain ⟨σ,hs,hrest⟩ := admissibleExtension ctrl Γ ρ t ht
  have hv := exactPaddedVector ctrl t ht
  have hhead : closedValue ctrl (σ.vector .here 1)=closedValue ctrl t :=
    (congrArg (closedValue ctrl) (hs 1)).trans hv.2.2.2
  have hscalar : closedValue ctrl (σ.vector .here 0)=((actualOrdinalNorm (closedValue ctrl t)+1 : Nat) : Ordinal) :=
    (congrArg (closedValue ctrl) (hs 0)).trans hv.2.2.1
  refine ⟨σ,?_,?_,?_,?_,hrest⟩
  · rw [hhead]; exact hcnf
  · rw [hhead]; exact hpos
  · rw [hhead]; exact hbound
  · rw [hhead,hscalar]
end LogicLineages.PermittedControl.SelectedPolynomialLift.Proof
