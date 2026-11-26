module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchWindowTargets
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchCodeProof
open NumberedWindowInternalFreshProbeDispatchWindowTargets
open NumberedWindowProbeCode (code)
open NumberedWindowPairAlgorithm (pair)

private theorem squareGap {s t : Nat} (h : s < t) : s*s+s < t*t := by
  have hst : s+1 ≤ t := Nat.succ_le_of_lt h
  have hsq := Nat.mul_le_mul hst hst
  have hs : (s+1)*(s+1) = s*s+s+s+1 := by
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul]
    omega
  rw [hs] at hsq
  omega

/-- This is the actual polynomial used in the current raw type code,
not the older max-square Nat.pair or a supplied decoder assumption. -/
private theorem pairComponents {a b c d : Nat} (h : pair a b = pair c d) :
    a = c ∧ b = d := by
  let s := a+b
  let t := c+d
  have hp : s*s+a = t*t+c := h
  have ha : a ≤ s := by dsimp [s]; omega
  have hc : c ≤ t := by dsimp [t]; omega
  have hsum : s = t := by
    rcases Nat.lt_trichotomy s t with hlt | heq | hgt
    · have hg := squareGap hlt
      omega
    · exact heq
    · have hg := squareGap hgt
      omega
  rw [hsum] at hp
  have hl : a = c := Nat.add_left_cancel hp
  have hr : b = d := by dsimp [s,t] at hsum; omega
  exact ⟨hl,hr⟩

theorem exact_ProbeCodeInjective : ExactProbeCodeInjective := by
  intro a b h
  induction a generalizing b with
  | ground =>
    cases b with
    | ground => rfl
    | arrow ρ υ => simp only [code] at h; omega
  | arrow σ τ ihσ ihτ =>
    cases b with
    | ground => simp only [code] at h; omega
    | arrow ρ υ =>
      change pair (code σ) (code τ) + 1 = pair (code ρ) (code υ) + 1 at h
      obtain ⟨hl,hr⟩ := pairComponents (Nat.add_right_cancel h)
      rw [ihσ ρ hl,ihτ υ hr]

#print axioms exact_ProbeCodeInjective
end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchCodeProof
