module
public import LogicLineages.PermittedControl.InitialPeelingTargets
public import LogicLineages.PermittedControl.LinearReturnProof
public import LogicLineages.PermittedControl.SensitiveHigherProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem firstEntry_shift (f : Nat → Nat) (A target : Ordinal.{0}) (i j : Nat)
    (hbefore : ∀ k < i, ¬ (target ≤ (descentWith f)^[k] A ∧ (descentWith f)^[k] A < target+Ordinal.omega0))
    (hentry : FirstEntry f ((descentWith f)^[i] A) target j) : FirstEntry f A target (i+j) := by
  have hc (k : Nat) : (descentWith f)^[i+k] A=(descentWith f)^[k] ((descentWith f)^[i] A) := by
    rw [Nat.add_comm i k,Function.iterate_add_apply]
  refine ⟨?_,?_,?_⟩
  · rw [hc]
    exact hentry.1
  · rw [hc]
    exact hentry.2.1
  · intro k hk hhit
    by_cases hki : k < i
    · exact hbefore k hki hhit
    · obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le (le_of_not_gt hki)
      subst k
      rw [hc] at hhit
      exact hentry.2.2 r (by omega) hhit

 theorem firstEntry_compose (f : Nat → Nat) (A middle target : Ordinal.{0}) (i j : Nat)
    (hA : A < epsilonZero) (hgap : target+Ordinal.omega0 ≤ middle)
    (hi : FirstEntry f A middle i) (hj : FirstEntry f ((descentWith f)^[i] A) target j) :
    FirstEntry f A target (i+j) := by
  apply firstEntry_shift f A target i j _ hj
  intro k hk hhit
  have hlow := hgap.trans (hi.1.trans (trajectory_antitone f A hA hk.le))
  exact (not_lt_of_ge hlow) hhit.2

 theorem firstEntry_prepend (f : Nat → Nat) (A target : Ordinal.{0}) (j : Nat)
    (hskip : target+Ordinal.omega0 ≤ A) (hj : FirstEntry f (descentWith f A) target j) :
    FirstEntry f A target (1+j) := by
  apply firstEntry_shift f A target 1 j _ hj
  intro k hk hhit
  have : k=0 := by omega
  subst k
  exact (not_lt_of_ge hskip) hhit.2

 theorem initial_radius_bounds (mu nu delta : Ordinal.{0}) :
    20 ≤ initialPeelingRadius mu nu delta ∧ actualOrdinalNorm mu ≤ initialPeelingRadius mu nu delta ∧
    actualOrdinalNorm nu ≤ initialPeelingRadius mu nu delta ∧ actualOrdinalNorm delta ≤ initialPeelingRadius mu nu delta := by
  dsimp [initialPeelingRadius]
  omega

end LogicLineages.PermittedControl
