module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.GroundAdmissibleComparisonTargets
public import LogicLineages.OrdinalComparison.WWOriginalDomainProof
public import LogicLineages.OrdinalComparison.WWOriginalPositivityProof
public import LogicLineages.OrdinalComparison.WWUnitObservationProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.GroundAdmissibleComparisonProof
open GroundAdmissibleComparison Source Source.OriginalDomain Source.ForwardTranslation RecursorFreeVector
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem ground_type {Γ : List Ty} {σ : Ty}
    (hΓ : ∀ τ ∈ Γ, τ = Ty.ground) (x : Variable Γ σ) : σ = Ty.ground := by
  induction x with
  | here => exact hΓ _ List.mem_cons_self
  | there x ih =>
      apply ih
      intro τ hτ
      exact hΓ τ (List.mem_cons_of_mem _ hτ)

private theorem ground_closed_value (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ = Ty.ground)
    (ρ : AdmissibleSubstitution Γ) (c : OrdinalComponent Γ) :
    ∃ n : Nat, 0 < n ∧ valuation ρ c = (n : Ordinal) := by
  rcases c with ⟨σ, x, j⟩
  have hs := ground_type hΓ x
  cases hs
  have hj : j = 0 := Fin.eq_zero j
  subst j
  obtain ⟨n, hn⟩ := originalClosedScalarFinite _ (ρ.graded x 0)
  have hp := originalClosedGradePositive 0 _ (ρ.graded x 0)
  rw [hn] at hp
  refine ⟨n, ?_, hn⟩
  exact_mod_cast hp

theorem exactGroundValuations : GroundAdmissibleComparisonTargets.ExactGroundValuations := by
  intro Γ hΓ
  constructor
  · intro ρ
    let ν : OrdinalComponent Γ → Nat := fun c =>
      Classical.choose (ground_closed_value Γ hΓ ρ c)
    refine ⟨ν, ?_, ?_⟩
    · intro c
      exact (Classical.choose_spec (ground_closed_value Γ hΓ ρ c)).1
    · funext c
      exact (Classical.choose_spec (ground_closed_value Γ hΓ ρ c)).2
  · intro ν hp
    let raw : Variable Γ .ground → Nat := fun x => ν ⟨.ground, x, 0⟩ - 1
    refine ⟨UnitObservation.substitution raw, ?_⟩
    funext c
    rcases c with ⟨σ, x, j⟩
    have hs := ground_type hΓ x
    cases hs
    have hj : j = 0 := Fin.eq_zero j
    subst j
    rw [(UnitObservation.Proof.groundValue Γ raw x).2]
    have hn : raw x + 1 = ν ⟨.ground, x, 0⟩ := by
      have hpos := hp ⟨.ground, x, 0⟩
      dsimp only [raw]
      omega
    exact congrArg (fun n : Nat => (n : Ordinal)) hn

theorem vectorRelationAt : GroundAdmissibleComparisonTargets.VectorRelationAt := by
  intro Γ n m mode a b ρ ν hρ
  have values : ∀ {k : Nat} (v : OrdinalVector Γ k) (j : Nat),
      vectorAtValue v ρ j = sourceVectorAtValue v ν j := by
    intro k v j
    change denote (valuation ρ) (ordinalVectorAt v j) =
      denote (fun c => (ν c : Ordinal)) (ordinalVectorAt v j)
    rw [hρ]
  simp only [relation, sourceRelation, SourceComparisonAt, values,
    Bool.false_eq_true, ↓reduceIte]

theorem universalComparison : GroundAdmissibleComparisonTargets.UniversalComparison := by
  intro Γ hΓ n m mode a b
  have domain := exactGroundValuations Γ hΓ
  constructor
  · intro h ν hp
    obtain ⟨ρ, hρ⟩ := domain.2 ν hp
    exact (vectorRelationAt Γ n m mode a b ρ ν hρ).mp (h ρ)
  · intro h ρ
    obtain ⟨ν, hp, hρ⟩ := domain.1 ρ
    exact (vectorRelationAt Γ n m mode a b ρ ν hρ).mpr (h ν hp)

theorem actualCanonicalComparison : GroundAdmissibleComparisonTargets.ActualCanonicalComparison := by
  intro Γ hΓ τ a b
  obtain ⟨av, hav, _⟩ :=
    AdmissibleAssignment.actualAdmissibleAssignmentGenerated Γ τ OrdinalSyntax.defaultPolicy a
  obtain ⟨bv, hbv, _⟩ :=
    AdmissibleAssignment.actualAdmissibleAssignmentGenerated Γ τ OrdinalSyntax.defaultPolicy b
  exact ⟨av, bv, hav, hbv, fun mode =>
    universalComparison Γ hΓ τ.level τ.level mode av bv⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.GroundAdmissibleComparisonProof
