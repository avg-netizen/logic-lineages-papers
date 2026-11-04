module
public import LogicLineages.OrdinalComparison.ParametricSourceOneTargets
public import LogicLineages.OrdinalComparison.ParametricSourceAdditionProof
public import LogicLineages.OrdinalComparison.SourceAdditionCompletionIdentityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceOne.Proof
open LogicLineages.ComputabilityKnowledge
open SourceAdditionCompletion SourceSortCompletion

theorem identity_assignment (Γ : List Ty) :
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy
      (.app (identity (Γ := Γ)) .zeroC) = some (identityVector Γ) :=
  SourceAdditionCompletion.Proof.identity_zero_assignment Γ

private theorem collapse_one_equal (G : Nat → Nat) (hm : StrictMono G) (hi : ∀ n,n ≤ G n)
    {Γ} (ρ : OrdinalComponent Γ → Ordinal) (t s : OrdinalExpression Γ) (n m : Nat)
    (ht : ParametricSourceSuccessor.denoteWith G ρ t = (n : Ordinal))
    (hs : ParametricSourceSuccessor.denoteWith G ρ s = (m : Ordinal)) :
    ParametricSourceSuccessor.denoteWith G ρ (.collapse .one t) =
      ParametricSourceSuccessor.denoteWith G ρ (.collapse .one s) ↔ n=m := by
  rw [ParametricSourceAddition.Proof.collapse_one_value G hm hi ρ t n ht,
    ParametricSourceAddition.Proof.collapse_one_value G hm hi ρ s m hs]
  constructor
  · intro h
    have hn : G (n+2)+1 = G (m+2)+1 := Nat.cast_injective h
    have he : G (n+2)=G (m+2) := by omega
    have hh := hm.injective he
    omega
  · intro h
    rw [h]

private theorem succ_identity (G : Nat → Nat) (hm : StrictMono G) (hi : ∀ n,n ≤ G n) {Γ} (ρ : OrdinalComponent Γ → Nat) (x : Variable Γ .ground) :
    ParametricSourceAddition.Equation G ρ (successorProbe x) (.app identity .zeroC) ↔ input ρ x = 2 := by
  let r : OrdinalComponent Γ → Ordinal := fun c => ((ρ c + 1 : Nat) : Ordinal)
  have h1 : ParametricSourceSuccessor.denoteWith G r (.one : OrdinalExpression Γ) = ((1 : Nat) : Ordinal) := by simp [ParametricSourceSuccessor.denoteWith]
  have hx : ParametricSourceSuccessor.denoteWith G r (.var ⟨.ground, x, 0⟩) = ((input ρ x + 1 : Nat) : Ordinal) := rfl
  have ht := ParametricSourceAddition.Proof.add_value G r _ _ _ _ h1 hx
  have h2 := ParametricSourceAddition.Proof.add_value G r _ _ _ _ h1 h1
  have h3 := ParametricSourceAddition.Proof.add_value G r _ _ _ _ h2 h1
  have h4 := ParametricSourceAddition.Proof.add_value G r _ _ _ _ h3 h1
  have hpair := collapse_one_equal G hm hi r _ _ _ _ ht h4
  constructor
  · rintro ⟨va, vb, ha, hb, he⟩
    rw [ParametricSourceSuccessor.Proof.probe_assignment Γ] at ha
    rw [identity_assignment] at hb
    cases Option.some.inj ha
    cases Option.some.inj hb
    have hn := hpair.mp (by simpa only [identityVector, r] using he)
    omega
  · intro h
    refine ⟨_, _, ParametricSourceSuccessor.Proof.probe_assignment Γ x, identity_assignment Γ, ?_⟩
    exact hpair.mpr (by omega)



theorem identitySourceEquation : Targets.IdentitySourceEquation :=
  ⟨identity_assignment,fun G hm hi Γ ρ x => succ_identity G hm hi ρ x⟩

theorem exactOne : Targets.ExactOne := by
  intro G hm hi
  constructor
  · intro u v d
    simp only [OneWitness,succ_identity G hm hi,
      ParametricSourceAddition.Proof.add_witness G hm hi,input,extend,singletonVal]
    omega
  · intro u
    simp only [OneFormula,succ_identity G hm hi,
      ParametricSourceAddition.Proof.add_formula G hm hi,input,extend,singletonVal]
    constructor
    · rintro ⟨v,hv,hu⟩
      omega
    · intro h
      subst u
      exact ⟨2,rfl,rfl⟩

theorem actualGammaOne : Targets.ActualGammaOne := by
  intro b
  have h := ParametricCoefficientOne.Proof.actualGammaCoefficientOne b
  exact exactOne _ h.1 h.2.1
end LogicLineages.OrdinalComparison.Source.ParametricSourceOne.Proof
