module

public import LogicLineages.RL.CrossLatticeProof
public import LogicLineages.RL.EnvironmentMixtureProof
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace LogicLineages.RL.Policy.CrossObstructionProof

theorem actualFrameworkEnvironmentMixtures (S : Alphabet) :
    Targets.ActualFrameworkEnvironmentMixtures S := by
  intro agents μ ν w
  obtain ⟨η, he, hv, _⟩ := EnvironmentMixtureProof.environmentMixtureValue S w μ ν
  exact ⟨η, fun p => hv (agentKernel agents p)⟩

def halfWeight : RatOpenUnit := ⟨1 / 2, by constructor <;> norm_num⟩

/-- Integer gaps cannot support arbitrarily repeated strict intermediate
values. Strong induction uses only the source's exact midpoint instances. -/
theorem crossOrderObstruction : Targets.CrossOrderObstruction := by
  classical
  intro F G d hlat hmix
  rintro ⟨f, g, hcross, p, μ, ν, hp⟩
  have hd := CrossLatticeProof.denominator_pos d
  have impossible : ∀ n : ℕ, ∀ (α β : G.Environment) (l r : ℤ),
      F.value p (g α) = (l : ℝ) / (d.val : ℝ) →
      F.value p (g β) = (r : ℝ) / (d.val : ℝ) →
      G.value (f p) α < G.value (f p) β → r - l = (n : ℤ) → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro α β l r hl hr hab hgap
        obtain ⟨γ, hγ⟩ := hmix α β halfWeight
        have hmid : G.value (f p) γ = (G.value (f p) α + G.value (f p) β) / 2 := by
          rw [hγ]
          norm_num [halfWeight]
          ring
        have hag : G.value (f p) α < G.value (f p) γ := by linarith
        have hgb : G.value (f p) γ < G.value (f p) β := by linarith
        obtain ⟨m, hm⟩ := hlat p (g γ)
        have hlm : l < m := by
          have hs := (hcross p p α γ).mp hag
          rw [hl, hm] at hs
          exact_mod_cast (div_lt_div_iff_of_pos_right hd).mp hs
        have hmr : m < r := by
          have hs := (hcross p p γ β).mp hgb
          rw [hm, hr] at hs
          exact_mod_cast (div_lt_div_iff_of_pos_right hd).mp hs
        have hnonneg : 0 ≤ m - l := by omega
        have hsmall : (m - l).toNat < n := by omega
        exact ih (m - l).toNat hsmall α γ l m hl hm hag (by omega)
  obtain ⟨l, hl⟩ := hlat p (g μ)
  obtain ⟨r, hr⟩ := hlat p (g ν)
  have hlr : l < r := by
    have hs := (hcross p p μ ν).mp hp
    rw [hl, hr] at hs
    exact_mod_cast (div_lt_div_iff_of_pos_right hd).mp hs
  exact impossible (r - l).toNat μ ν l r hl hr hp (by omega)

theorem crossFromDeterministicRewards : Targets.CrossFromDeterministicRewards := by
  intro F G d hsource htarget
  exact crossOrderObstruction F G d
    (CrossLatticeProof.deterministicRewardLattice F d hsource) htarget

theorem actualScaledDDCrossObstruction : Targets.ActualScaledDDCrossObstruction := by
  intro S T d targetAgents
  exact crossOrderObstruction (scaledDD S d) (framework T targetAgents Kind.stochastic) d
    (CrossLatticeProof.scaledDDCalibration S d).1 (actualFrameworkEnvironmentMixtures T targetAgents)

end LogicLineages.RL.Policy.CrossObstructionProof
