module
public import Mathlib.Data.Finsupp.SMul
public import LogicLineages.OrdinalComparison.SourceFiniteExponentProjectionTargets

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.SourceFiniteExponentProjection.Proof

theorem exactCoefficients : Targets.ExactCoefficients := by
  constructor
  · intro g n
    rfl
  · intro e c he
    ext n
    have hne : e ≠ (n : Ordinal) := ne_of_gt ((Ordinal.natCast_lt_omega0 n).trans_le he)
    simp [finitePart, Finsupp.comapDomain_apply, hne, hne.symm]

theorem signedOperations : Targets.SignedOperations := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext n
    rfl
  · intro g h
    ext n
    simp [finitePart, Finsupp.comapDomain_apply]
  · intro g
    ext n
    simp [finitePart, Finsupp.comapDomain_apply]
  · intro k g
    ext n
    simp [finitePart, Finsupp.comapDomain_apply, Finsupp.smul_apply]

theorem exactShift : Targets.ExactShift := by
  intro g
  have hs : Function.Injective (fun e : Ordinal.{0} => e + 1) := by
    intro e f hef
    apply Order.succ_injective
    simpa only [Order.succ_eq_add_one] using hef
  ext n
  change Finsupp.mapDomain (fun e : Ordinal.{0} => e + 1) g (n : Ordinal) =
    Finsupp.mapDomain Nat.succ (finitePart g) n
  cases n with
  | zero =>
      have ho : (0 : Ordinal.{0}) ∉ Set.range (fun e : Ordinal.{0} => e + 1) := by
        rintro ⟨e, he⟩
        have hp : (0 : Ordinal) < e + 1 :=
          (show (0 : Ordinal) ≤ e from zero_le).trans_lt (Order.lt_add_one_iff.mpr le_rfl)
        change e + 1 = 0 at he
        rw [he] at hp
        exact lt_irrefl _ hp
      have hn : 0 ∉ Set.range Nat.succ := by
        rintro ⟨n, he⟩
        omega
      rw [Nat.cast_zero, Finsupp.mapDomain_notin_range g 0 ho,
        Finsupp.mapDomain_notin_range (finitePart g) 0 hn]
  | succ n =>
      rw [Nat.cast_succ]
      rw [Finsupp.mapDomain_apply hs g (n : Ordinal),
        Finsupp.mapDomain_apply Nat.succ_injective (finitePart g) n]
      rfl

end LogicLineages.OrdinalComparison.Source.SourceFiniteExponentProjection.Proof
