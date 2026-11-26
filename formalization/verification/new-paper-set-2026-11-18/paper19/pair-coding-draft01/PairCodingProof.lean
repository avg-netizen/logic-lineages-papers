module
public import LogicLineages.ControlSensitivityCurrent.PairCodingTargets
public import Mathlib.Data.List.Permutation
public import Lean.Elab.Tactic.Omega
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PairCoding
section
variable (q : Nat → Nat) (qm : StrictMono q) (hg : ∀ n, 2*q n < q (n+1))
include qm hg
private theorem sorted_pair_unique (a b c d : Nat) (hab : a ≤ b) (hcd : c ≤ d)
    (h : q a + q b = q c + q d) :
    a = c ∧ b = d := by
  have hmono := qm.monotone
  have hgap := hg
  have hbd : b ≤ d := by
    by_contra hn
    have hdb : d + 1 ≤ b := by omega
    have hsmall := hmono hcd
    have hlarge := (hgap d).trans_le (hmono hdb)
    omega
  have hdb : d ≤ b := by
    by_contra hn
    have hbd' : b + 1 ≤ d := by omega
    have hsmall := hmono hab
    have hlarge := (hgap b).trans_le (hmono hbd')
    omega
  have he : b = d := by omega
  subst d
  refine ⟨qm.injective (by omega), rfl⟩

private theorem pair_cases (a b c d : Nat) :
    q a + q b = q c + q d ↔ (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  constructor
  · intro h
    rcases le_total a b with hab | hba
    · rcases le_total c d with hcd | hdc
      · exact Or.inl (sorted_pair_unique q qm hg a b c d hab hcd h)
      · exact Or.inr (sorted_pair_unique q qm hg a b d c hab hdc (by omega))
    · rcases le_total c d with hcd | hdc
      · have hh := sorted_pair_unique q qm hg b a c d hba hcd (by omega)
        exact Or.inr ⟨hh.2, hh.1⟩
      · have hh := sorted_pair_unique q qm hg b a d c hba hdc (by omega)
        exact Or.inl ⟨hh.2, hh.1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> omega

end

theorem sortedWitness : PairCodingTargets.SortedWitness := by
  intro q hp hg a b low high difference
  have qm : StrictMono q := by
    apply strictMono_nat_of_lt_succ
    intro n
    have := hg n
    omega
  rw [pair_cases q qm hg]
  constructor
  · rintro ⟨hp, hd⟩
    rcases hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · subst low
      subst high
      have hab : a ≤ b := by omega
      simp only [min_eq_left hab, max_eq_right hab, true_and]
      omega
    · subst high
      subst low
      have hba : b ≤ a := by omega
      simp only [min_eq_right hba, max_eq_left hba, true_and]
      omega
  · rintro ⟨rfl, rfl, rfl⟩
    constructor
    · rcases le_total a b with h | h
      · exact Or.inl ⟨(min_eq_left h).symm, (max_eq_right h).symm⟩
      · exact Or.inr ⟨(max_eq_left h).symm, (min_eq_right h).symm⟩
    · have h : min a b ≤ max a b := min_le_max
      omega


theorem pairCoding : PairCodingTargets.PairCoding := by
  intro q hp hg a b c d
  have qm : StrictMono q := by
    apply strictMono_nat_of_lt_succ
    intro n
    have := hg n
    omega
  rw [pair_cases q qm hg]
  change ((a=c ∧ b=d) ∨ (a=d ∧ b=c)) ↔
    (([a,b] : List Nat) : Multiset Nat) = (([c,d] : List Nat) : Multiset Nat)
  rw [Multiset.coe_eq_coe, List.perm_pair]
  simp
#audit_namespace LogicLineages.ControlSensitivityCurrent.PairCoding
end LogicLineages.ControlSensitivityCurrent.PairCoding
