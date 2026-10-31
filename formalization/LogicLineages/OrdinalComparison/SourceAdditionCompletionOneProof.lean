module
public import LogicLineages.OrdinalComparison.SourceAdditionCompletionIdentityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAdditionCompletion.Proof
open LogicLineages.ComputabilityKnowledge
open WWOrdinalTermSemantics WWOrdinalTermSemanticsProof
open SourceSortCompletion

-- Keep enormous closed control/collapse values symbolic during elaboration.
-- All equalities are proved by the checked finite-head theorem, never evaluated.
attribute [local irreducible] Phi actualCollapse

private theorem succ_assignment {Γ} (x : Variable Γ .ground) :
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (successorProbe x) =
      some (fun _ => .collapse .one (.add .one (.var ⟨.ground, x, 0⟩))) := by
  apply congrArg some
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp [AdmissibleAssignment.application, AdmissibleAssignment.box,
    AdmissibleAssignment.boxTail, ordinalBoxPositive, ordinalVectorAt, Ty.level]

private theorem succ_identity {Γ} (ρ : OrdinalComponent Γ → Nat) (x : Variable Γ .ground) :
    Equation ρ (successorProbe x) (.app identity .zeroC) ↔ input ρ x = 2 := by
  let r : OrdinalComponent Γ → Ordinal := fun c => ((ρ c + 1 : Nat) : Ordinal)
  have h1 : denote r (.one : OrdinalExpression Γ) = ((1 : Nat) : Ordinal) := by simp [denote]
  have hx : denote r (.var ⟨.ground, x, 0⟩) = ((input ρ x + 1 : Nat) : Ordinal) := rfl
  have ht := add_value r _ _ _ _ h1 hx
  have h2 := add_value r _ _ _ _ h1 h1
  have h3 := add_value r _ _ _ _ h2 h1
  have h4 := add_value r _ _ _ _ h3 h1
  have hpair := collapse_one_equal r _ _ _ _ ht h4
  constructor
  · rintro ⟨va, vb, ha, hb, he⟩
    rw [succ_assignment] at ha
    rw [identity_zero_assignment] at hb
    cases Option.some.inj ha
    cases Option.some.inj hb
    have hn := hpair.mp (by simpa only [identityZeroVector, r] using he)
    omega
  · intro h
    refine ⟨_, _, succ_assignment x, identity_zero_assignment Γ, ?_⟩
    exact hpair.mpr (by omega)


theorem one_formula (u : Nat) : OneFormula u ↔ u = 1 := by
  simp only [OneFormula, succ_identity, add_formula, input, extend, singletonVal]
  constructor
  · rintro ⟨v, hv, hu⟩
    omega
  · intro h
    subst u
    exact ⟨2, rfl, rfl⟩

end LogicLineages.OrdinalComparison.Source.SourceAdditionCompletion.Proof
