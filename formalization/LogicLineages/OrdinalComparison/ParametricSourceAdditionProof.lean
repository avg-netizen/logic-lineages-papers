module
public import LogicLineages.OrdinalComparison.ParametricSourceAdditionAtomicProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceAddition.Proof
open SourceAdditionCompletion SourceSortCompletion
variable (G : Nat → Nat) (hm : StrictMono G) (hi : ∀ n : Nat, n ≤ G n)
include hm hi in
theorem weighted_equality {Γ} (ρ : OrdinalComponent Γ → Nat) (a b c d : Atom Γ) :
    Equation G ρ (eraser a b) (eraser c d) ↔
      3 * atomValue ρ a + atomValue ρ b = 3 * atomValue ρ c + atomValue ρ d := by
  constructor
  · rintro ⟨va, vb, ha, hb, he⟩
    rw [eraser_assignment] at ha hb
    cases Option.some.inj ha
    cases Option.some.inj hb
    rw [eraser_value G hm hi, eraser_value G hm hi] at he
    have hn : G (3 * atomValue ρ a + atomValue ρ b + 8) + 1 =
        G (3 * atomValue ρ c + atomValue ρ d + 8) + 1 := by exact_mod_cast he
    have hphi : G (3 * atomValue ρ a + atomValue ρ b + 8) =
        G (3 * atomValue ρ c + atomValue ρ d + 8) := by omega
    have := hm.injective hphi
    omega
  · intro h
    refine ⟨_, _, eraser_assignment a b, eraser_assignment c d, ?_⟩
    rw [eraser_value G hm hi, eraser_value G hm hi, h]

include hm hi in
theorem add_witness {Γ} (ρ : OrdinalComponent Γ → Nat)
    (a b c : Variable Γ .ground) (d : Nat) :
    AddWitness G ρ a b c d ↔ input ρ a + input ρ b = input ρ c ∧ d = 3 * input ρ b := by
  simp only [AddWitness, weighted_equality G hm hi, atomValue, input, extend]
  omega

include hm hi in
theorem add_formula {Γ} (ρ : OrdinalComponent Γ → Nat)
    (a b c : Variable Γ .ground) :
    AddFormula G ρ a b c ↔ input ρ a + input ρ b = input ρ c := by
  simp [AddFormula, add_witness G hm hi]


theorem weightedEquality : Targets.WeightedEquality := by
  intro G hm hi Γ ρ a b c d
  exact weighted_equality G hm hi ρ a b c d

theorem exactAddition : Targets.ExactAddition := by
  intro G hm hi Γ ρ a b c
  exact ⟨add_witness G hm hi ρ a b c,add_formula G hm hi ρ a b c⟩

theorem actualGammaAddition : Targets.ActualGammaAddition := by
  intro b Γ ρ x y z
  have h := ParametricCoefficientOne.Proof.actualGammaCoefficientOne b
  exact exactAddition _ h.1 h.2.1 Γ ρ x y z
end LogicLineages.OrdinalComparison.Source.ParametricSourceAddition.Proof
