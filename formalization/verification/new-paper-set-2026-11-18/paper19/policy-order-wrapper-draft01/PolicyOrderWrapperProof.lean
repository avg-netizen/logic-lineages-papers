module
public import LogicLineages.ControlSensitivityCurrent.PolicyOrderWrapperAssignmentProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyOrderWrapper
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open GroundEquivalence ParametricSourceSuccessor

theorem raw_of_scalar (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (ρ : OrdinalComponent Γ → Nat) (t : OriginalTerm Γ .ground) (n : Nat)
    (h : CompositeEraser.Scalar p f (fun c => ((ρ c+1 : Nat) : Ordinal)) t n) :
    PolicyCollision.rawScalar p f ρ t = n := by
  obtain ⟨v,hv,he⟩ := h
  unfold PolicyCollision.rawScalar
  rw [hv]
  change OriginalDomain.finiteValue (denoteWith f _ (v 0)) = n
  rw [he]
  exact OriginalDomain.originalFiniteValueCalibration n

theorem three_value (f : Nat → Nat) {Γ} (ν : OrdinalComponent Γ → Ordinal) :
    denoteWith f ν three = ((3 : Nat) : Ordinal) := by
  have h1 : denoteWith f ν (.one : OrdinalExpression Γ) = ((1 : Nat) : Ordinal) := rfl
  have h2 := ParametricSourceAddition.Proof.add_value f ν _ _ _ _ h1 h1
  exact ParametricSourceAddition.Proof.add_value f ν _ _ 2 1 h2 h1

theorem five_value (f : Nat → Nat) {Γ} (ν : OrdinalComponent Γ → Ordinal) :
    denoteWith f ν five = ((5 : Nat) : Ordinal) := by
  have h1 : denoteWith f ν (.one : OrdinalExpression Γ) = ((1 : Nat) : Ordinal) := rfl
  have h2 := ParametricSourceAddition.Proof.add_value f ν _ _ _ _ h1 h1
  have h4 := ParametricSourceAddition.Proof.add_value f ν _ _ _ _ h2 h2
  exact ParametricSourceAddition.Proof.add_value f ν _ _ 4 1 h4 h1

theorem identityValue : PolicyOrderWrapperTargets.Identity := by
  intro f hf p Γ ρ t
  have hc := FullAddition.completeAddition.2.2.2 f hf
  obtain ⟨v,hv,he⟩ := ((FullCollision.completeCollision f hf p Γ ρ).1 t).2
  apply raw_of_scalar p f ρ _ _
  refine ⟨_,identity_application p t v hv,?_⟩
  have ha := ParametricSourceAddition.Proof.add_value f _ _ _ _ _ (three_value f _) he
  have hh := ParametricSourceAddition.Proof.collapse_one_value f hc.1
    (fun n => (hc.2.1 n).le) _ _ _ ha
  simpa only [PolicyCollision.g,Nat.add_comm 3] using hh

theorem constantValue : PolicyOrderWrapperTargets.Constant := by
  intro f hf p Γ ρ t
  have hc := FullAddition.completeAddition.2.2.2 f hf
  obtain ⟨v,hv,he⟩ := ((FullCollision.completeCollision f hf p Γ ρ).1 t).2
  apply raw_of_scalar p f ρ _ _
  refine ⟨_,constant_application p t v hv,?_⟩
  have ha := ParametricSourceAddition.Proof.add_value f _ _ _ _ _ (five_value f _) he
  have hh := ParametricSourceAddition.Proof.collapse_one_value f hc.1
    (fun n => (hc.2.1 n).le) _ _ _ ha
  simpa only [PolicyCollision.g,Nat.add_comm 5] using hh

theorem magnifyValue : PolicyOrderWrapperTargets.Magnify := by
  intro f hf p Γ ρ t
  have hc := FullAddition.completeAddition.2.2.2 f hf
  have ht := ((FullCollision.completeCollision f hf p Γ ρ).1 t).2
  have hz : CompositeEraser.Scalar p f (fun c => ((ρ c+1 : Nat) : Ordinal))
      (.zeroC : OriginalTerm Γ .ground) 1 := ⟨_,rfl,rfl⟩
  have hh := (CompositeEraser.finiteClosure p f hc.1 (fun n => (hc.2.1 n).le)
    Γ _ t .zeroC _ 1 ht hz).1
  apply raw_of_scalar p f ρ _ _
  simpa only [GroundEquivalence.magnify,PolicyCollision.g,Nat.add_assoc] using hh

theorem orderConversion : PolicyOrderWrapperTargets.OrderConversion := by
  intro f hf p Γ ρ a b
  have hc := FullAddition.completeAddition.2.2.2 f hf
  have hg : StrictMono (PolicyCollision.g f) := by
    intro x y h
    exact Nat.add_lt_add_right (hc.1 (Nat.add_lt_add_right h 2)) 1
  change PolicyCollision.rawScalar p f ρ (.app GroundEquivalence.constant (magnify a)) ≤
    PolicyCollision.rawScalar p f ρ (.app GroundEquivalence.identity (magnify b)) ↔ _
  rw [constantValue f hf,identityValue f hf,magnifyValue f hf,magnifyValue f hf]
  rw [hg.le_iff_le]
  constructor
  · intro h
    by_contra hn
    have hx : 3*PolicyCollision.rawScalar p f ρ b+3 ≤
        3*PolicyCollision.rawScalar p f ρ a+3 := by omega
    have hm := hg.monotone hx
    omega
  · intro h
    let x := 3*PolicyCollision.rawScalar p f ρ a+3
    let y := 3*PolicyCollision.rawScalar p f ρ b+3
    have h1 := hg (show x < x+1 by omega)
    have h2 := hg (show x+1 < x+2 by omega)
    have h3 := hg (show x+2 < y by dsimp [x,y]; omega)
    dsimp [x,y] at h1 h2 h3
    omega
end LogicLineages.ControlSensitivityCurrent.PolicyOrderWrapper
